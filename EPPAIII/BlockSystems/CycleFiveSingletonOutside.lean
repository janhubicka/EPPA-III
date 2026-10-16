import EPPAIII.BlockSystems.CycleFiveProperOutsideAction

/-!
# Canonical singleton labels for the matching C5 cross relation

A ten-vertex EPPA host of the induced five-cycle with one outside
vertex seeing exactly one selected vertex must have five distinct
singleton profiles. Rather than assume a matching to a previously
indexed outside half, we produce an actual equivalence from Fin 5
onto the outside vertices, with the top vertex indexed by x
adjacent to exactly the selected vertex x.

With vertex-transitivity, genuine EPPA lifts give a cyclic action
on this canonically indexed top graph and equal half-edge counts
make it C5 or its complement. No coherent EPPA lifts or
imprimitivity system is assumed.
-/

namespace EPPAIII.BlockSystems

/-- If one outside neighbourhood is a singleton, the actual
outside vertices admit an equivalence indexed by their unique
selected neighbours. The equality of profiles is part of the
conclusion, not a labelling hypothesis. -/
theorem cycleFive_eppa_singleton_outside_equiv
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ f : Fin 5 ≃ {u : W // u ∈ finiteOutside e},
      ∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val = {x} := by
  classical
  have hNonempty : finiteNeighbourhoodProfile H e w ≠ ∅ := by
    intro hEmpty
    have hZero : (finiteNeighbourhoodProfile H e w).card = 0 := by
      rw [hEmpty]
      simp
    omega
  have hNonfull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5)) := by
    intro hFull
    have hFive : (finiteNeighbourhoodProfile H e w).card = 5 := by
      rw [hFull]
      decide
    omega
  obtain ⟨f,hLabels⟩ :=
    cycleFive_eppa_proper_profile_outside_equiv
      H e heppa hTen w hw hNonempty hNonfull
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hOne
  let q : Equiv.Perm (Fin 5) := Equiv.addRight (-a)
  let f' : Fin 5 ≃ {u : W // u ∈ finiteOutside e} := q.trans f
  refine ⟨f',?_⟩
  intro x
  calc
    finiteNeighbourhoodProfile H e (f' x).val =
        (finiteNeighbourhoodProfile H e w).image
          (Equiv.addRight (q x)) := hLabels (q x)
    _ = ({a} : Finset (Fin 5)).image
          (Equiv.addRight (q x)) := by rw [ha]
    _ = {x} := by
      simp only [Finset.image_singleton]
      change ({a + (x + -a)} : Finset (Fin 5)) = {x}
      congr 1
      abel

/-- Under the unique selected-neighbour labels, genuine EPPA lifts
rotate the actual outside graph, which has exactly five edges.
Consequently the outside graph is the canonical C5 or its complement. -/
theorem cycleFive_eppa_singleton_outside_graph_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ f : Fin 5 ≃ {u : W // u ∈ finiteOutside e},
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val = {x}) ∧
      (H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
       H.comap (fun x => (f x).val) =
         (SimpleGraph.cycleGraph 5)ᶜ) := by
  classical
  obtain ⟨f,hLabels⟩ :=
    cycleFive_eppa_singleton_outside_equiv H e heppa hTen w hw hOne
  have hNonempty : finiteNeighbourhoodProfile H e w ≠ ∅ := by
    intro hEmpty
    have hZero : (finiteNeighbourhoodProfile H e w).card = 0 := by
      rw [hEmpty]
      simp
    omega
  have hNonfull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5)) := by
    intro hFull
    have hFive : (finiteNeighbourhoodProfile H e w).card = 5 := by
      rw [hFull]
      decide
    omega
  have hInj : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W) :=
    (cycleFive_eppa_proper_profile_saturates_outside
      H e heppa hTen w hw hNonempty hNonfull).2
  let outside : Fin 5 → W := fun x => (f x).val
  have hOut (x : Fin 5) : outside x ∈ finiteOutside e := (f x).property
  have hRot : ∀ d : Fin 5,
      IsGraphAutomorphism (H.comap outside) (Equiv.addRight d) := by
    intro d
    exact canonical_outside_graph_automorphism
      (SimpleGraph.cycleGraph 5) H e heppa
      (Equiv.addRight d) (cycleFive_translate_graph_automorphism d)
      (fun x : Fin 5 => ({x} : Finset (Fin 5)))
      outside hOut hLabels hInj (by intro x; simp)
  have hSide :
      ((CliqueCovers.outsideInducedGraph H e).comap f).edgeSet.ncard =
        (SimpleGraph.cycleGraph 5).edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      (SimpleGraph.cycleGraph 5) H e heppa.1 f hTrans
  have hSideGraph :
      (CliqueCovers.outsideInducedGraph H e).comap f =
        H.comap outside := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hFive : (H.comap outside).edgeSet.ncard = 5 := by
    rw [hSideGraph,cycleFive_edge_count_five] at hSide
    exact hSide
  exact ⟨f,hLabels,cycleFive_invariant_five_edges_two_forms
    (H.comap outside) hRot hFive⟩

end EPPAIII.BlockSystems
