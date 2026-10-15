import EPPAIII.BlockSystems.CycleFiveOutsideEquiv
import EPPAIII.BlockSystems.CycleFiveInvariantFourForms
import EPPAIII.BlockSystems.OutsideProfileCanonicalAction
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# The actual outside graph in the C5 cross-degree-two case

Once a ten-vertex C5 EPPA host has cross-degree two, its outside
profiles form a unique five-element cyclic orbit, giving an actual
equivalence from Fin 5 to the complementary vertices.

Every base rotation has a genuine EPPA lift, and uniqueness of the
profiles determines its action on these outside vertices. Therefore
the induced outside graph is invariant under all five rotations.
There are four invariant graphs, and equal internal edge numbers in
a vertex-transitive host exclude the empty and complete forms.

This theorem does not assume an action on the outside half or an
a priori outside partition. It does not yet exclude the complementary
C5 as the outside graph: that final distinction needs an additional
transitivity invariant (triangle counts).
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Cyclic shifting of adjacent-pair profiles commutes with
rotation of the selected base. -/
theorem cycleFive_edge_shift_equivariant (d : Fin 5) :
    ∀ x : Fin 5,
      cycleFiveEdgePairShift ((Equiv.addRight d) x) =
        (cycleFiveEdgePairShift x).image (Equiv.addRight d) := by
  decide +revert

/-- The same equivariance for the diagonal-pair orbit. -/
theorem cycleFive_diagonal_shift_equivariant (d : Fin 5) :
    ∀ x : Fin 5,
      cycleFiveDiagonalPairShift ((Equiv.addRight d) x) =
        (cycleFiveDiagonalPairShift x).image (Equiv.addRight d) := by
  decide +revert

/-- Actual EPPA extensions act by cyclic shifts on the unique
outside profiles, hence on the induced outside adjacency relation. -/
theorem cycleFive_canonical_outside_graph_invariant
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (outside : Fin 5 → W)
    (hOutside : ∀ x : Fin 5, outside x ∈ finiteOutside e)
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (outside x) =
          cycleFiveEdgePairShift x) ∨
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (outside x) =
          cycleFiveDiagonalPairShift x)) :
    ∀ d : Fin 5,
      IsGraphAutomorphism (H.comap outside) (Equiv.addRight d) := by
  intro d
  rcases hLabels with hEdge | hDiagonal
  · exact canonical_outside_graph_automorphism
      (SimpleGraph.cycleGraph 5) H e heppa
      (Equiv.addRight d) (cycleFive_translate_graph_automorphism d)
      cycleFiveEdgePairShift outside hOutside hEdge hInjective
      (cycleFive_edge_shift_equivariant d)
  · exact canonical_outside_graph_automorphism
      (SimpleGraph.cycleGraph 5) H e heppa
      (Equiv.addRight d) (cycleFive_translate_graph_automorphism d)
      cycleFiveDiagonalPairShift outside hOutside hDiagonal hInjective
      (cycleFive_diagonal_shift_equivariant d)

/-- The induced outside graph has one of four invariant forms. -/
theorem cycleFive_canonical_outside_graph_four_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (outside : Fin 5 → W)
    (hOutside : ∀ x : Fin 5, outside x ∈ finiteOutside e)
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (outside x) =
          cycleFiveEdgePairShift x) ∨
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (outside x) =
          cycleFiveDiagonalPairShift x)) :
    H.comap outside = ⊥ ∨
      H.comap outside = SimpleGraph.cycleGraph 5 ∨
      H.comap outside = (SimpleGraph.cycleGraph 5)ᶜ ∨
      H.comap outside = ⊤ :=
  cycleFive_invariant_graph_four_forms (H.comap outside)
    (cycleFive_canonical_outside_graph_invariant
      H e heppa outside hOutside hInjective hLabels)

/-- The five-cycle has exactly five edges. -/
theorem cycleFive_edge_count_five :
    (SimpleGraph.cycleGraph 5).edgeSet.ncard = 5 := by
  classical
  have h : (SimpleGraph.cycleGraph 5).edgeFinset.card = 5 := by decide
  simpa only [← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard] using h

/-- The complete graph on five vertices has ten edges. -/
theorem cycleFive_complete_edge_count_ten :
    (⊤ : SimpleGraph (Fin 5)).edgeSet.ncard = 10 := by
  classical
  have h : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by decide
  simpa only [← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard] using h

/-- Equal half-edge counts in the transitive host exclude
the empty and complete outside graph. -/
theorem cycleFive_canonical_outside_graph_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (f : (Fin 5) ≃ {w : W // w ∈ finiteOutside e})
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          cycleFiveEdgePairShift x) ∨
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          cycleFiveDiagonalPairShift x)) :
    H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
      H.comap (fun x => (f x).val) =
        (SimpleGraph.cycleGraph 5)ᶜ := by
  classical
  let outside : Fin 5 → W := fun x => (f x).val
  have hOutside (x : Fin 5) : outside x ∈ finiteOutside e :=
    (f x).property
  have hFour :
      H.comap outside = ⊥ ∨
        H.comap outside = SimpleGraph.cycleGraph 5 ∨
        H.comap outside = (SimpleGraph.cycleGraph 5)ᶜ ∨
        H.comap outside = ⊤ :=
    cycleFive_canonical_outside_graph_four_forms
      H e heppa outside hOutside hInjective hLabels
  have hSide :
      ((CliqueCovers.outsideInducedGraph H e).comap f).edgeSet.ncard =
        (SimpleGraph.cycleGraph 5).edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      (SimpleGraph.cycleGraph 5) H e heppa.1 f hTrans
  have hSideGraph :
      ((CliqueCovers.outsideInducedGraph H e).comap f) =
        H.comap outside := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hCount : (H.comap outside).edgeSet.ncard = 5 := by
    rw [hSideGraph, cycleFive_edge_count_five] at hSide
    exact hSide
  rcases hFour with hEmpty | hCycle | hComplement | hComplete
  · have hZero : (H.comap outside).edgeSet.ncard = 0 := by
      rw [hEmpty]
      simp
    omega
  · exact Or.inl hCycle
  · exact Or.inr hComplement
  · have hTen : (H.comap outside).edgeSet.ncard = 10 := by
      rw [hComplete]
      exact cycleFive_complete_edge_count_ten
    omega

/-- The actual C5 EPPA host has a canonically labelled outside
half whose induced graph is a five-cycle or its complement,
provided all outside vertices have exactly two selected neighbours. -/
theorem cycleFive_eppa_degree_two_outside_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2) :
    ∃ f : (Fin 5) ≃ {w : W // w ∈ finiteOutside e},
      ((∀ x : Fin 5,
          finiteNeighbourhoodProfile H e (f x).val =
            cycleFiveEdgePairShift x) ∨
        (∀ x : Fin 5,
          finiteNeighbourhoodProfile H e (f x).val =
            cycleFiveDiagonalPairShift x)) ∧
      (H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
        H.comap (fun x => (f x).val) =
          (SimpleGraph.cycleGraph 5)ᶜ) := by
  classical
  obtain ⟨f,hLabels⟩ :=
    cycleFive_eppa_outside_equiv_of_two_neighbours
      H e heppa hTen hDegree
  have hInjective : Set.InjOn
      (finiteNeighbourhoodProfile H e) (finiteOutside e : Set W) :=
    (cycleFive_eppa_outside_pair_profile_classification
      H e heppa hTen hDegree).2
  exact ⟨f,hLabels,
    cycleFive_canonical_outside_graph_two_forms
      H e heppa hTrans f hInjective hLabels⟩

end EPPAIII.BlockSystems
