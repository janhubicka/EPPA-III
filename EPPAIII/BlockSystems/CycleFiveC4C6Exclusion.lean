import EPPAIII.BlockSystems.OutsideCommonPairOrbits
import EPPAIII.BlockSystems.CycleFiveTransitivity
import EPPAIII.BlockSystems.CanonicalC4C6Cross

/-!
# The canonical C4 plus C6 cross relation cannot be EPPA for C5

The source of Lemma 3.18 considers a 2-regular bipartite cross graph
on 5+5 vertices. Its disconnected candidate C4 ⊔ C6 has one pair of
selected vertices with two common outside neighbours.

Here we prove the exact exclusion for any EPPA host whose selected
and outside vertices can be labelled so that the cross-incidence
matrix is the canonical C4 ⊔ C6 matrix. The outside relabelling is
an actual equivalence with the complementary half, and the selected
relabelling is an arbitrary permutation. No equivariance of these
labellings is assumed.

The independent remaining step for Lemma 3.18 is to derive such
labellings from the abstract disconnected 2-regular graph alternative.
-/

namespace EPPAIII.BlockSystems

/-- The canonical cross-incidence matrix identifies all outside
common-neighbour cardinalities under arbitrary labels of both
halves. -/
theorem canonical_c4c6_cross_common_neighbour_table
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (σ : Equiv.Perm (Fin 5))
    (φ : Fin 5 ≃ {w : W // w ∉ Set.range e})
    (hCross : ∀ x z : Fin 5,
      H.Adj (e (σ x)) (φ z).1 ↔ canonicalC4C6Cross x z)
    (x y : Fin 5) :
    (outsideCommonNeighbourFinset H e (σ x) (σ y)).card =
      canonicalC4C6CommonCount x y := by
  classical
  have hInfo (w : W)
      (hw : w ∈ outsideCommonNeighbourFinset H e (σ x) (σ y)) :
      w ∉ Set.range e ∧ H.Adj (e (σ x)) w ∧ H.Adj (e (σ y)) w := by
    simpa [outsideCommonNeighbourFinset] using hw
  have hOutside (w : W)
      (hw : w ∈ outsideCommonNeighbourFinset H e (σ x) (σ y)) :
      w ∉ Set.range e :=
    (hInfo w hw).1
  unfold canonicalC4C6CommonCount
  refine Finset.card_bij'
    (fun w hw => φ.symm ⟨w,hOutside w hw⟩)
    (fun z _ => (φ z).1) ?_ ?_ ?_ ?_
  · intro w hw
    have hX : canonicalC4C6Cross x
        (φ.symm ⟨w,hOutside w hw⟩) :=
      (hCross x (φ.symm ⟨w,hOutside w hw⟩)).mp (by
        simpa using (hInfo w hw).2.1)
    have hY : canonicalC4C6Cross y
        (φ.symm ⟨w,hOutside w hw⟩) :=
      (hCross y (φ.symm ⟨w,hOutside w hw⟩)).mp (by
        simpa using (hInfo w hw).2.2)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨hX,hY⟩⟩
  · intro z hz
    have hAdj :=
      (Finset.mem_filter.mp hz).2
    change (φ z).1 ∈ outsideCommonNeighbourFinset
      H e (σ x) (σ y)
    simp only [outsideCommonNeighbourFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨(φ z).2,
      (hCross x z).mpr hAdj.1,
      (hCross y z).mpr hAdj.2⟩
  · intro w hw
    simpa using congrArg Subtype.val
      (φ.apply_symm_apply ⟨w,hOutside w hw⟩)
  · intro z hz
    simpa using φ.symm_apply_apply z

/-- Genuine EPPA for the induced C5 is incompatible with any
cross-incidence matrix isomorphic to the canonical C4 ⊔ C6. -/
theorem cycleFive_not_eppa_with_c4c6_cross_matrix
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (σ : Equiv.Perm (Fin 5))
    (φ : Fin 5 ≃ {w : W // w ∉ Set.range e})
    (hCross : ∀ x z : Fin 5,
      H.Adj (e (σ x)) (φ z).1 ↔ canonicalC4C6Cross x z) :
    False := by
  classical
  let a : Fin 5 := σ 0
  let b : Fin 5 := σ 1
  have hPair :
      (outsideCommonNeighbourFinset H e a b).card = 2 := by
    calc
      (outsideCommonNeighbourFinset H e a b).card =
          canonicalC4C6CommonCount 0 1 :=
        canonical_c4c6_cross_common_neighbour_table
          H e σ φ hCross 0 1
      _ = 2 := by decide
  have hUnique : ∀ u v : Fin 5, u ≠ v →
      (outsideCommonNeighbourFinset H e u v).card = 2 →
      ({u,v} : Finset (Fin 5)) = {a,b} := by
    intro u v huv hCount
    let i : Fin 5 := σ.symm u
    let j : Fin 5 := σ.symm v
    have hNe : i ≠ j := σ.symm.injective.ne huv
    have hCanon : canonicalC4C6CommonCount i j = 2 := by
      calc
        canonicalC4C6CommonCount i j =
            (outsideCommonNeighbourFinset H e (σ i) (σ j)).card :=
          (canonical_c4c6_cross_common_neighbour_table
            H e σ φ hCross i j).symm
        _ = (outsideCommonNeighbourFinset H e u v).card := by
          simp [i,j]
        _ = 2 := hCount
    have hCanonPair :
        ({i,j} : Finset (Fin 5)) = {0,1} :=
      (canonicalC4C6_unique_double_common_pair
        i j hNe).mp hCanon
    have hImage := congrArg
      (fun S : Finset (Fin 5) => S.image σ) hCanonPair
    simpa [i,j,a,b] using hImage
  exact no_unique_outside_double_common_pair_of_transitive_eppa
    (SimpleGraph.cycleGraph 5) H e heppa
    cycleFive_vertex_transitive (by decide)
    a b (σ.injective.ne (by decide)) hPair hUnique

end EPPAIII.BlockSystems
