import EPPAIII.BlockSystems.CycleFiveComplementEppa
import EPPAIII.EPPA.ProfileOrbitBound

/-!
# Actual C5 neighbourhood degrees under complement and reindexing

If w lies outside the chosen C5 copy in H, its neighbours among
the five selected vertices become non-neighbours after complementing
both graphs. Reindexing the selected base by the explicit cyclic
self-complementing permutation preserves cardinalities.

Consequently the new outside cross-degree is exactly 5-k, where
k was the old one. This avoids a hidden assumption that one may
complement the host while keeping its selected graph unchanged:
both the host and the base are complemented and the base is
genuinely relabelled.
-/

namespace EPPAIII.BlockSystems

/-- The selected profile of an outside point in the complemented
C5 EPPA embedding is exactly the permuted complement of its old
profile. This is a true equality of finite sets, not merely a
counting identity. -/
theorem cycleFive_complement_reindexed_profile_eq
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (w : W) (hw : w ∈ finiteOutside e) :
    finiteNeighbourhoodProfile Hᶜ
      (EPPAIII.relabelEmbedding e cycleFiveDoubleIndex) w =
        ((finiteNeighbourhoodProfile H e w)ᶜ).image
          cycleFiveDoubleIndex.symm := by
  classical
  let p := cycleFiveDoubleIndex
  let S := finiteNeighbourhoodProfile H e w
  let T := finiteNeighbourhoodProfile Hᶜ
    (EPPAIII.relabelEmbedding e p) w
  have hwNot : w ∉ Set.range e := by
    simpa [finiteOutside] using hw
  have hPoint (x : (Fin 5)) :
      x ∈ T ↔ p x ∉ S := by
    have hNe : w ≠ e (p x) := by
      intro h
      exact hwNot ⟨p x,h.symm⟩
    simp only [T,S,finiteNeighbourhoodProfile,
      Finset.mem_filter, Finset.mem_univ,true_and]
    change Hᶜ.Adj w (e (p x)) ↔
      ¬ H.Adj w (e (p x))
    constructor
    · intro h
      exact ((SimpleGraph.compl_adj H w (e (p x))).mp h).2
    · intro h
      exact (SimpleGraph.compl_adj H w (e (p x))).mpr ⟨hNe,h⟩
  change T = (Sᶜ).image p.symm
  ext x
  constructor
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨p x, ?_, p.symm_apply_apply x⟩
    exact Finset.mem_compl.mpr ((hPoint x).mp hx)
  · intro hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
    have hyx' : y = p x := by
      have hh := congrArg p hyx
      simpa only [p.apply_symm_apply] using hh
    apply (hPoint x).mpr
    rw [← hyx']
    exact Finset.mem_compl.mp hy

/-- For every outside vertex, the two profile cardinalities sum
to five, the size of the selected five-cycle. -/
theorem cycleFive_complement_reindexed_profile_card_sum_five
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (w : W) (hw : w ∈ finiteOutside e) :
    (finiteNeighbourhoodProfile Hᶜ
        (EPPAIII.relabelEmbedding e cycleFiveDoubleIndex) w).card +
      (finiteNeighbourhoodProfile H e w).card = 5 := by
  classical
  let S := finiteNeighbourhoodProfile H e w
  have hProfile :=
    cycleFive_complement_reindexed_profile_eq H e w hw
  have hImageCard :
      ((Sᶜ).image cycleFiveDoubleIndex.symm).card =
      (Sᶜ).card :=
    Finset.card_image_of_injective _ cycleFiveDoubleIndex.symm.injective
  rw [hProfile,hImageCard]
  change (Sᶜ).card + S.card = 5
  have hBound : S.card ≤ Fintype.card (Fin 5) := by
    simpa using Finset.card_le_univ S
  rw [Finset.card_compl]
  have hCycle : Fintype.card (Fin 5) = 5 := by decide
  omega


/-- Relabelling the selected C5 does not change the actual
complementary vertex set of the host. -/
theorem cycleFive_relabel_outside_eq
    {W : Type*} [Fintype W] (e : (Fin 5) ↪ W) :
    finiteOutside
      (EPPAIII.relabelEmbedding e cycleFiveDoubleIndex) =
        finiteOutside e := by
  classical
  ext w
  simp only [finiteOutside,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · intro hw ⟨x,hx⟩
    apply hw
    refine ⟨cycleFiveDoubleIndex.symm x,?_⟩
    change e (cycleFiveDoubleIndex (cycleFiveDoubleIndex.symm x)) = w
    simpa using hx
  · intro hw ⟨x,hx⟩
    exact hw ⟨cycleFiveDoubleIndex x,hx⟩

end EPPAIII.BlockSystems
