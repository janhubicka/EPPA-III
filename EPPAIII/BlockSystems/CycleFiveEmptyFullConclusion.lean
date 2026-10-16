import EPPAIII.BlockSystems.CycleFiveEmptyFullRigidity
import EPPAIII.BlockSystems.TransitiveSeparatedHalf
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The full complementary C5 conclusion of Claim 3.19

A vertex-transitive ten-vertex EPPA witness containing an induced C5
has its complementary induced graph isomorphic to C5, with no
imprimitivity hypothesis. The proof separates two profile cases:

* A proper outside profile: verified five-element orbit saturation
  gives canonical cyclic labels and a C5/complementary-C5 graph.
* All outside profiles empty/full: degree rigidity makes them uniform.
  The host (or its complement) has no cross edges, and transitivity
  transports the selected connected component to the outside half.

The complement of the five-cycle is another five-cycle, witnessed
by multiplication by two on Fin 5. All equivalences and graph
identifications are actual Lean constructions, not assumptions about
coherent EPPA extensions or designated imprimitivity blocks.
-/

namespace EPPAIII.BlockSystems

/-- Multiplication by two, with inverse multiplication by three,
on the five-cycle's finite cyclic vertex set. -/
def cycleFiveDoubleIndex : Equiv.Perm (Fin 5) where
  toFun := fun x => 2 * x
  invFun := fun x => 3 * x
  left_inv := by decide
  right_inv := by decide

/-- The complementary C5 is transported to the ordinary C5
by the explicit multiplication-by-two permutation. -/
theorem cycleFive_doubleIndex_complement_adj :
    ∀ x y : Fin 5,
      (SimpleGraph.cycleGraph 5)ᶜ.Adj x y ↔
        (SimpleGraph.cycleGraph 5).Adj
          (cycleFiveDoubleIndex x) (cycleFiveDoubleIndex y) := by
  decide

/-- In particular the complement of C5 is connected. -/
theorem cycleFive_complement_preconnected :
    (SimpleGraph.cycleGraph 5)ᶜ.Preconnected := by
  let p := cycleFiveDoubleIndex
  let hom : (SimpleGraph.cycleGraph 5) →g
      (SimpleGraph.cycleGraph 5)ᶜ :=
    { toFun := p.symm
      map_rel' := by
        intro u v huv
        have h := cycleFive_doubleIndex_complement_adj
          (p.symm u) (p.symm v)
        apply h.mpr
        simpa [p] using huv }
  intro x y
  have hReach :=
    (SimpleGraph.cycleGraph_preconnected (p x) (p y)).map hom
  simpa [hom,p] using hReach

/-- All-empty or all-full profiles force the complementary
induced graph to be exactly C5 under some actual equivalence.
This uses no EPPA; the only global assumption is vertex
transitivity of the host. -/
theorem cycleFive_empty_full_outside_is_cycle
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (he : IsInducedGraphEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (hProfiles : ∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w = ∅ ∨
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))) :
    ∃ f : Fin 5 ≃ {u : W // u ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 := by
  classical
  have hDouble :
      Fintype.card W = 2 * Fintype.card (Fin 5) := by
    simpa using hTen
  rcases cycleFive_transitive_empty_full_profiles_uniform
    H e hTen hTrans hProfiles with hEmpty | hFull
  · have hSeparated : ∀ u : W, u ∈ finiteOutside e →
        ∀ x : Fin 5, ¬ H.Adj u (e x) := by
      intro u hu x hadj
      have hx : x ∈ finiteNeighbourhoodProfile H e u := by
        simpa [finiteNeighbourhoodProfile] using hadj
      rw [hEmpty u hu] at hx
      simpa using hx
    exact transitive_outside_equiv_of_connected_separated
      (SimpleGraph.cycleGraph 5)
      SimpleGraph.cycleGraph_preconnected
      H e he hDouble hTrans hSeparated
  · have hComplementInduced :
        IsInducedGraphEmbedding (SimpleGraph.cycleGraph 5)ᶜ Hᶜ e :=
      induced_embedding_complement (SimpleGraph.cycleGraph 5) H e he
    have hSeparated : ∀ u : W, u ∈ finiteOutside e →
        ∀ x : Fin 5, ¬ Hᶜ.Adj u (e x) := by
      intro u hu x hCompAdj
      have hx : x ∈ finiteNeighbourhoodProfile H e u := by
        rw [hFull u hu]
        exact Finset.mem_univ x
      have hAdj : H.Adj u (e x) := by
        simpa [finiteNeighbourhoodProfile] using hx
      exact ((SimpleGraph.compl_adj H u (e x)).mp hCompAdj).2 hAdj
    obtain ⟨f,hOutsideComp⟩ :=
      transitive_outside_equiv_of_connected_separated
        (SimpleGraph.cycleGraph 5)ᶜ
        cycleFive_complement_preconnected
        Hᶜ e hComplementInduced hDouble
        (transitive_complement H hTrans) hSeparated
    have hComapComplement :
        Hᶜ.comap (fun x => (f x).val) =
          (H.comap (fun x => (f x).val))ᶜ := by
      apply SimpleGraph.ext
      funext x y
      apply propext
      have hNe : (f x).val ≠ (f y).val ↔ x ≠ y := by
        constructor
        · intro h hxy
          exact h (congrArg (fun z : {u : W // u ∈ finiteOutside e} =>
            z.val) (congrArg f hxy))
        · intro hxy h
          apply hxy
          apply f.injective
          exact Subtype.ext h
      change ((f x).val ≠ (f y).val ∧
          ¬ H.Adj (f x).val (f y).val) ↔
        (x ≠ y ∧ ¬ H.Adj (f x).val (f y).val)
      exact and_congr hNe Iff.rfl
    rw [hComapComplement] at hOutsideComp
    have hOutsideOriginal :=
      congrArg (fun J : SimpleGraph (Fin 5) => Jᶜ) hOutsideComp
    refine ⟨f,?_⟩
    simpa using hOutsideOriginal

/-- The exact complementary-half conclusion needed by Claim 3.19.
No imprimitivity hypothesis, outside block action, or coherent
choice of EPPA lifts is assumed. -/
theorem cycleFive_eppa_outside_is_cycle
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10) :
    ∃ f : Fin 5 ≃ {u : W // u ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 := by
  classical
  by_cases hAll : ∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w = ∅ ∨
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))
  · exact cycleFive_empty_full_outside_is_cycle
      H e heppa.1 hTrans hTen hAll
  · have hProper :
        ∃ w : W, w ∈ finiteOutside e ∧
          finiteNeighbourhoodProfile H e w ≠ ∅ ∧
          finiteNeighbourhoodProfile H e w ≠
            (Finset.univ : Finset (Fin 5)) := by
      by_contra hNo
      apply hAll
      intro w hw
      by_cases hEmpty : finiteNeighbourhoodProfile H e w = ∅
      · exact Or.inl hEmpty
      · right
        by_contra hFull
        exact hNo ⟨w,hw,hEmpty,hFull⟩
    obtain ⟨w,hw,hNe,hFull⟩ := hProper
    obtain ⟨f,_,hForms⟩ :=
      cycleFive_eppa_proper_outside_two_forms
        H e heppa hTrans hTen w hw hNe hFull
    rcases hForms with hCycle | hComplement
    · exact ⟨f,hCycle⟩
    · let f' : Fin 5 ≃ {u : W // u ∈ finiteOutside e} :=
        cycleFiveDoubleIndex.symm.trans f
      refine ⟨f',?_⟩
      apply SimpleGraph.ext
      funext x y
      apply propext
      have hOld :
          H.Adj (f (cycleFiveDoubleIndex.symm x)).val
            (f (cycleFiveDoubleIndex.symm y)).val ↔
            (SimpleGraph.cycleGraph 5)ᶜ.Adj
              (cycleFiveDoubleIndex.symm x)
              (cycleFiveDoubleIndex.symm y) := by
        change (H.comap (fun z => (f z).val)).Adj
          (cycleFiveDoubleIndex.symm x)
          (cycleFiveDoubleIndex.symm y) ↔
          (SimpleGraph.cycleGraph 5)ᶜ.Adj
            (cycleFiveDoubleIndex.symm x)
            (cycleFiveDoubleIndex.symm y)
        rw [hComplement]
      have hIso := cycleFive_doubleIndex_complement_adj
        (cycleFiveDoubleIndex.symm x)
        (cycleFiveDoubleIndex.symm y)
      change H.Adj (f (cycleFiveDoubleIndex.symm x)).val
        (f (cycleFiveDoubleIndex.symm y)).val ↔
          (SimpleGraph.cycleGraph 5).Adj x y
      exact hOld.trans (by simpa using hIso)

end EPPAIII.BlockSystems
