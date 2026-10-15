import EPPAIII.BlockSystems.CycleFiveOutsideAction
import EPPAIII.DoubleCover.TriangleTransport

/-!
# The actual degree-two C5 EPPA host is a cyclic double

A ten-vertex transitive EPPA witness for the induced five-cycle with
two neighbours in the selected cycle at every outside vertex has a
canonical outside index coming from neighbourhood pairs.

The outside graph is one of C5 or its complement; the cross relation
is an adjacent-pair or diagonal-pair orbit. We identify the actual host
with one of four finite doubles. An exact ordered-triangle certificate
rules out the complementary outside graph, leaving two cyclic doubles.

All host identifications use a constructed equivalence, no presumed
coherence of EPPA lifts, no outside partition, and no assumption that
the induced complementary graph is a five-cycle.
-/

namespace EPPAIII.BlockSystems

/-- An explicitly decidable adjacency predicate for the five-cycle. -/
def cycleFiveExplicitAdjacent (x y : Fin 5) : Prop :=
  x + 1 = y ∨ y + 1 = x

/-- This finite predicate is exactly Mathlib's five-cycle adjacency. -/
theorem cycleFiveExplicitAdjacent_iff :
    ∀ x y : Fin 5,
      cycleFiveExplicitAdjacent x y ↔ (SimpleGraph.cycleGraph 5).Adj x y := by
  decide

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Adjacency relation of the four explicit two-layer five-cycle hosts.
The outside vertex y sees the selected pair {y,y+1} or {y,y+2}. -/
def cycleFiveDoubleRelation (topComplement diagonal : Bool)
    (u v : Bool × Fin 5) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then cycleFiveExplicitAdjacent u.2 v.2
    else if topComplement then
      u.2 ≠ v.2 ∧ ¬ cycleFiveExplicitAdjacent u.2 v.2
    else cycleFiveExplicitAdjacent u.2 v.2
  else if u.1 = false then
    u.2 ∈ (if diagonal then
      cycleFiveDiagonalPairShift v.2 else cycleFiveEdgePairShift v.2)
  else
    v.2 ∈ (if diagonal then
      cycleFiveDiagonalPairShift u.2 else cycleFiveEdgePairShift u.2)

/-- The canonical graph is genuinely undirected and loopless. -/
def cycleFiveDoubleGraph (topComplement diagonal : Bool) :
    SimpleGraph (Bool × Fin 5) :=
  SimpleGraph.fromRel (cycleFiveDoubleRelation topComplement diagonal)

instance (topComplement diagonal : Bool) :
    DecidableRel (cycleFiveDoubleGraph topComplement diagonal).Adj := by
  intro u v
  change Decidable (u ≠ v ∧
    (cycleFiveDoubleRelation topComplement diagonal u v ∨
      cycleFiveDoubleRelation topComplement diagonal v u))
  infer_instance

/-- Symmetrising the explicit relation creates no extra edges. -/
theorem cycleFiveDoubleGraph_adj_iff :
    ∀ topComplement diagonal : Bool,
    ∀ u v : Bool × Fin 5,
      (cycleFiveDoubleGraph topComplement diagonal).Adj u v ↔
        cycleFiveDoubleRelation topComplement diagonal u v := by
  decide

/-- The finite ordered triangle count through a vertex. -/
def cycleFiveDoubleOrderedTriangles (topComplement diagonal : Bool)
    (u : Bool × Fin 5) : ℕ :=
  ((Finset.univ : Finset ((Bool × Fin 5) × (Bool × Fin 5))).filter
    (fun yz =>
      (cycleFiveDoubleGraph topComplement diagonal).Adj u yz.1 ∧
      (cycleFiveDoubleGraph topComplement diagonal).Adj u yz.2 ∧
      (cycleFiveDoubleGraph topComplement diagonal).Adj yz.1 yz.2)).card

theorem cycleFiveDoubleOrderedTriangles_eq_actual
    (topComplement diagonal : Bool) (u : Bool × Fin 5) :
    cycleFiveDoubleOrderedTriangles topComplement diagonal u =
      (DoubleCover.orderedTrianglePairsAt
        (cycleFiveDoubleGraph topComplement diagonal) u).card := by
  classical
  unfold cycleFiveDoubleOrderedTriangles
  congr 1
  ext yz
  simp [DoubleCover.orderedTrianglePairsAt]

/-- The complementary outside C5 changes the ordered triangle
count between the designated lower and upper halves. -/
theorem cycleFiveDouble_bad_triangle_counts :
    cycleFiveDoubleOrderedTriangles true false (false,0) = 4 ∧
    cycleFiveDoubleOrderedTriangles true false (true,0) = 2 ∧
    cycleFiveDoubleOrderedTriangles true true (false,0) = 2 ∧
    cycleFiveDoubleOrderedTriangles true true (true,0) = 4 := by
  decide

/-- The other two forms have matching bottom/top triangle counts. -/
theorem cycleFiveDouble_surviving_triangle_counts :
    cycleFiveDoubleOrderedTriangles false false (false,0) = 6 ∧
    cycleFiveDoubleOrderedTriangles false false (true,0) = 6 ∧
    cycleFiveDoubleOrderedTriangles false true (false,0) = 0 ∧
    cycleFiveDoubleOrderedTriangles false true (true,0) = 0 := by
  decide

/-- Neither canonical double with a complementary upper five-cycle
is vertex-transitive. -/
theorem cycleFiveDouble_complement_top_not_transitive
    (diagonal : Bool) :
    ¬ IsVertexTransitive (cycleFiveDoubleGraph true diagonal) := by
  intro hTrans
  have hEqual :=
    DoubleCover.orderedTrianglePairsAt_card_transitive
      (cycleFiveDoubleGraph true diagonal) hTrans
      (false,0) (true,0)
  obtain ⟨h1,h2,h3,h4⟩ := cycleFiveDouble_bad_triangle_counts
  cases diagonal with
  | false =>
      rw [← cycleFiveDoubleOrderedTriangles_eq_actual true false (false,0),
          ← cycleFiveDoubleOrderedTriangles_eq_actual true false (true,0)] at hEqual
      omega
  | true =>
      rw [← cycleFiveDoubleOrderedTriangles_eq_actual true true (false,0),
          ← cycleFiveDoubleOrderedTriangles_eq_actual true true (true,0)] at hEqual
      omega

/-- The actual cross-edge relation is read directly from the
outside vertex's neighbourhood profile. -/
theorem cycleFive_cross_iff_profile_member
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (w : W) (x : Fin 5) :
    H.Adj (e x) w ↔ x ∈ finiteNeighbourhoodProfile H e w := by
  classical
  simpa [finiteNeighbourhoodProfile] using (H.adj_comm (e x) w)

/-- The four given layer restrictions determine the finite double. -/
theorem cycleFiveDouble_graph_eq_of_layer_data
    (J : SimpleGraph (Bool × Fin 5))
    (topComplement diagonal : Bool)
    (hBB : ∀ x y : Fin 5,
      J.Adj (false,x) (false,y) ↔ (SimpleGraph.cycleGraph 5).Adj x y)
    (hTT : ∀ x y : Fin 5,
      J.Adj (true,x) (true,y) ↔
        (if topComplement then
          x ≠ y ∧ ¬ (SimpleGraph.cycleGraph 5).Adj x y
         else (SimpleGraph.cycleGraph 5).Adj x y))
    (hBT : ∀ x y : Fin 5,
      J.Adj (false,x) (true,y) ↔
        x ∈ (if diagonal then
          cycleFiveDiagonalPairShift y else cycleFiveEdgePairShift y))
    (hTB : ∀ x y : Fin 5,
      J.Adj (true,x) (false,y) ↔
        y ∈ (if diagonal then
          cycleFiveDiagonalPairShift x else cycleFiveEdgePairShift x)) :
    J = cycleFiveDoubleGraph topComplement diagonal := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  cases b <;> cases c
  · rw [cycleFiveDoubleGraph_adj_iff]
    simpa [cycleFiveDoubleRelation, cycleFiveExplicitAdjacent_iff] using hBB x y
  · rw [cycleFiveDoubleGraph_adj_iff]
    simpa [cycleFiveDoubleRelation] using hBT x y
  · rw [cycleFiveDoubleGraph_adj_iff]
    simpa [cycleFiveDoubleRelation] using hTB x y
  · rw [cycleFiveDoubleGraph_adj_iff]
    simpa [cycleFiveDoubleRelation, cycleFiveExplicitAdjacent_iff] using hTT x y

/-- Match the actual host to one of the four explicit graph models,
using only the induced C5, an actual outside equivalence, its
two possible profile families, and its two possible outside graphs. -/
theorem cycleFive_actual_host_eq_canonical_double
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (he : IsInducedGraphEmbedding (SimpleGraph.cycleGraph 5) H e)
    (f : (Fin 5) ≃ {w : W // w ∈ finiteOutside e})
    (hTop :
      H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
      H.comap (fun x => (f x).val) = (SimpleGraph.cycleGraph 5)ᶜ)
    (hProfiles :
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        cycleFiveEdgePairShift x) ∨
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        cycleFiveDiagonalPairShift x)) :
    ∃ topComplement diagonal : Bool,
      H.comap (CliqueCovers.balancedHostEquiv e f) =
        cycleFiveDoubleGraph topComplement diagonal := by
  classical
  obtain ⟨topC,hTopAdj⟩ :
      ∃ topC : Bool, ∀ x y : Fin 5,
        H.Adj (f x).val (f y).val ↔
          (if topC then
            x ≠ y ∧ ¬ (SimpleGraph.cycleGraph 5).Adj x y
           else (SimpleGraph.cycleGraph 5).Adj x y) := by
    rcases hTop with hCycle | hComplement
    · refine ⟨false,?_⟩
      intro x y
      have h : (H.comap (fun x => (f x).val)).Adj x y ↔
          (SimpleGraph.cycleGraph 5).Adj x y := by rw [hCycle]
      simpa using h
    · refine ⟨true,?_⟩
      intro x y
      have h : (H.comap (fun x => (f x).val)).Adj x y ↔
          (SimpleGraph.cycleGraph 5)ᶜ.Adj x y := by rw [hComplement]
      simpa [SimpleGraph.compl_adj] using h
  obtain ⟨diag,hCrossAdj⟩ :
      ∃ diag : Bool, ∀ x y : Fin 5,
        H.Adj (e x) (f y).val ↔
          x ∈ (if diag then
            cycleFiveDiagonalPairShift y else cycleFiveEdgePairShift y) := by
    rcases hProfiles with hEdge | hDiagonal
    · refine ⟨false,?_⟩
      intro x y
      simpa [hEdge y] using
        (cycleFive_cross_iff_profile_member H e (f y).val x)
    · refine ⟨true,?_⟩
      intro x y
      simpa [hDiagonal y] using
        (cycleFive_cross_iff_profile_member H e (f y).val x)
  let phi := CliqueCovers.balancedHostEquiv e f
  let J : SimpleGraph (Bool × Fin 5) := H.comap phi
  have hBB (x y : Fin 5) :
      J.Adj (false,x) (false,y) ↔ (SimpleGraph.cycleGraph 5).Adj x y := by
    simpa [J,phi] using (he x y).symm
  have hTT (x y : Fin 5) :
      J.Adj (true,x) (true,y) ↔
        (if topC then
          x ≠ y ∧ ¬ (SimpleGraph.cycleGraph 5).Adj x y
         else (SimpleGraph.cycleGraph 5).Adj x y) := by
    simpa [J,phi] using hTopAdj x y
  have hBT (x y : Fin 5) :
      J.Adj (false,x) (true,y) ↔
        x ∈ (if diag then
          cycleFiveDiagonalPairShift y else cycleFiveEdgePairShift y) := by
    simpa [J,phi] using hCrossAdj x y
  have hTB (x y : Fin 5) :
      J.Adj (true,x) (false,y) ↔
        y ∈ (if diag then
          cycleFiveDiagonalPairShift x else cycleFiveEdgePairShift x) := by
    have hSym : H.Adj (f x).val (e y) ↔
        H.Adj (e y) (f x).val := H.adj_comm _ _
    simpa [J,phi] using (hSym.trans (hCrossAdj y x))
  exact ⟨topC,diag,
    cycleFiveDouble_graph_eq_of_layer_data
      J topC diag hBB hTT hBT hTB⟩

/-- Actual degree-two C5 EPPA hosts have one of two explicitly
identified finite adjacency patterns. The equivalence fixes the
distinguished bottom cycle and does not assume outside coordinates. -/
theorem cycleFive_eppa_degree_two_host_is_cyclic_double
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2) :
    ∃ (phi : Bool × Fin 5 ≃ W) (diagonal : Bool),
      (∀ x : Fin 5, phi (false,x) = e x) ∧
      H.comap phi = cycleFiveDoubleGraph false diagonal := by
  classical
  obtain ⟨f,hProfiles,hTop⟩ :=
    cycleFive_eppa_degree_two_outside_two_forms
      H e heppa hTrans hTen hDegree
  obtain ⟨topComplement,diagonal,hGraph⟩ :=
    cycleFive_actual_host_eq_canonical_double
      H e heppa.1 f hTop hProfiles
  let phi : Bool × Fin 5 ≃ W := CliqueCovers.balancedHostEquiv e f
  have hPullbackTrans : IsVertexTransitive (H.comap phi) :=
    CliqueCovers.transitive_comap_equiv H phi hTrans
  have hTopIsCycle : topComplement = false := by
    cases topComplement with
    | false => rfl
    | true =>
        have hBad : IsVertexTransitive
            (cycleFiveDoubleGraph true diagonal) := by
          rw [← hGraph]
          exact hPullbackTrans
        exact False.elim
          (cycleFiveDouble_complement_top_not_transitive diagonal hBad)
  refine ⟨phi,diagonal,?_,?_⟩
  · intro x
    exact CliqueCovers.balancedHostEquiv_false e f x
  · simpa only [hTopIsCycle] using hGraph

end EPPAIII.BlockSystems
