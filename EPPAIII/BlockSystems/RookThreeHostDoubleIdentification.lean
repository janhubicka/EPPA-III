import EPPAIII.BlockSystems.RookThreeDoubleAdjacency
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.EPPA.ProfileOrbitBound
import EPPAIII.BlockSystems.RookThreeNeighbourhoodOrbits

/-!
# Identifying an actual labelled R3 EPPA host as one of four rook doubles

The finite canonical triangle certificates are only useful after
showing that the actual host has the same adjacency matrix. Here
we establish the graph-theoretic bridge.

Assume an induced copy of the nine-vertex rook graph, a genuine
equivalence f onto the complementary half, an outside graph equal
to R3 or its complement, and cross profiles equal to all rook
neighbourhoods or all strict nonneighbourhoods.

We explicitly verify all four Boolean-layer adjacency cases under
the resulting balanced-host equivalence and identify the transported
host with one of the four canonical double graphs. EPPA and host
vertex transitivity are not assumed by this graph-identification
theorem; they are what will later provide the stated premises.
-/

namespace EPPAIII.BlockSystems

/-- The profile of a top vertex detects its adjacency to each
selected base vertex, using the undirected host relation. -/
theorem rook_cross_edge_iff_profile_member
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W) (w : W) (x : rookVertex) :
    H.Adj (e x) w ↔ x ∈ finiteNeighbourhoodProfile H e w := by
  classical
  simpa [finiteNeighbourhoodProfile] using (H.adj_comm (e x) w)

/-- Actual base rook profiles determine the forward cross layer. -/
theorem rook_cross_edge_open_profile
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (f : rookVertex ≃ {w : W // w ∈ finiteOutside e})
    (hOpen : ∀ y : rookVertex,
      finiteNeighbourhoodProfile H e (f y).val =
        rookOpenNeighbourhood y) (x y : rookVertex) :
    H.Adj (e x) (f y).val ↔ rookThreeGraph.Adj x y := by
  calc
    H.Adj (e x) (f y).val ↔
        x ∈ finiteNeighbourhoodProfile H e (f y).val :=
      rook_cross_edge_iff_profile_member H e (f y).val x
    _ ↔ x ∈ rookOpenNeighbourhood y := by rw [hOpen y]
    _ ↔ rookThreeGraph.Adj y x := by simp [rookOpenNeighbourhood]
    _ ↔ rookThreeGraph.Adj x y := rookThreeGraph.adj_comm y x

/-- Strict nonneighbourhood cross profiles encode the rook nonedges
on distinct indices. -/
theorem rook_cross_edge_strict_non_profile
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (f : rookVertex ≃ {w : W // w ∈ finiteOutside e})
    (hNon : ∀ y : rookVertex,
      finiteNeighbourhoodProfile H e (f y).val =
        rookStrictNonneighbours y) (x y : rookVertex) :
    H.Adj (e x) (f y).val ↔
      x ≠ y ∧ ¬ rookThreeGraph.Adj x y := by
  calc
    H.Adj (e x) (f y).val ↔
        x ∈ finiteNeighbourhoodProfile H e (f y).val :=
      rook_cross_edge_iff_profile_member H e (f y).val x
    _ ↔ x ∈ rookStrictNonneighbours y := by rw [hNon y]
    _ ↔ x ≠ y ∧ ¬ rookThreeGraph.Adj x y := by
      simp only [rookStrictNonneighbours, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne,hnAdj⟩
        exact ⟨hne,fun h => hnAdj ((rookThreeGraph.adj_comm x y).mp h)⟩
      · rintro ⟨hne,hnAdj⟩
        exact ⟨hne,fun h => hnAdj ((rookThreeGraph.adj_comm y x).mp h)⟩

/-- Identifies an arbitrary labelled two-half host graph with one
canonical rook double, with the outside and cross bits determined
by the corresponding actual graph and profile types. -/
theorem rook_actual_host_eq_canonical_double
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (he : IsInducedGraphEmbedding rookThreeGraph H e)
    (f : rookVertex ≃ {w : W // w ∈ finiteOutside e})
    (hTop :
      H.comap (fun x => (f x).val) = rookThreeGraph ∨
      H.comap (fun x => (f x).val) = rookThreeGraphᶜ)
    (hCross :
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        rookOpenNeighbourhood x) ∨
      (∀ x, finiteNeighbourhoodProfile H e (f x).val =
        rookStrictNonneighbours x)) :
    ∃ topComplement crossNonrook : Bool,
      H.comap (CliqueCovers.balancedHostEquiv e f) =
        rookDoubleGraph topComplement crossNonrook := by
  classical
  obtain ⟨topC,hTopAdj⟩ :
      ∃ topC : Bool, ∀ x y : rookVertex,
        H.Adj (f x).val (f y).val ↔
          (if topC then
            x ≠ y ∧ ¬ rookThreeGraph.Adj x y
           else rookThreeGraph.Adj x y) := by
    rcases hTop with hRook | hCompl
    · refine ⟨false,?_⟩
      intro x y
      have h : (H.comap (fun x => (f x).val)).Adj x y ↔
          rookThreeGraph.Adj x y := by rw [hRook]
      simpa using h
    · refine ⟨true,?_⟩
      intro x y
      have h : (H.comap (fun x => (f x).val)).Adj x y ↔
          rookThreeGraphᶜ.Adj x y := by rw [hCompl]
      simpa [SimpleGraph.compl_adj] using h
  obtain ⟨crossC,hCrossAdj⟩ :
      ∃ crossC : Bool, ∀ x y : rookVertex,
        H.Adj (e x) (f y).val ↔
          (if crossC then
            x ≠ y ∧ ¬ rookThreeGraph.Adj x y
           else rookThreeGraph.Adj x y) := by
    rcases hCross with hOpen | hNon
    · refine ⟨false,?_⟩
      intro x y
      simpa using (rook_cross_edge_open_profile H e f hOpen x y)
    · refine ⟨true,?_⟩
      intro x y
      simpa using (rook_cross_edge_strict_non_profile H e f hNon x y)
  have hReverse (x y : rookVertex) :
      (if crossC then
        y ≠ x ∧ ¬ rookThreeGraph.Adj y x
       else rookThreeGraph.Adj y x) ↔
      (if crossC then
        x ≠ y ∧ ¬ rookThreeGraph.Adj x y
       else rookThreeGraph.Adj x y) := by
    cases crossC
    · exact rookThreeGraph.adj_comm y x
    · constructor
      · rintro ⟨hne,hnAdj⟩
        exact ⟨hne.symm,fun h => hnAdj
          ((rookThreeGraph.adj_comm x y).mp h)⟩
      · rintro ⟨hne,hnAdj⟩
        exact ⟨hne.symm,fun h => hnAdj
          ((rookThreeGraph.adj_comm y x).mp h)⟩
  let phi := CliqueCovers.balancedHostEquiv e f
  let J : SimpleGraph (Bool × rookVertex) := H.comap phi
  have hBB (x y : rookVertex) :
      J.Adj (false,x) (false,y) ↔ rookThreeGraph.Adj x y := by
    simpa [J,phi] using (he x y).symm
  have hTT (x y : rookVertex) :
      J.Adj (true,x) (true,y) ↔
        (if topC then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y) := by
    simpa [J,phi] using hTopAdj x y
  have hBT (x y : rookVertex) :
      J.Adj (false,x) (true,y) ↔
        (if crossC then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y) := by
    simpa [J,phi] using hCrossAdj x y
  have hTB (x y : rookVertex) :
      J.Adj (true,x) (false,y) ↔
        (if crossC then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y) := by
    have hSym : H.Adj (f x).val (e y) ↔
        H.Adj (e y) (f x).val := H.adj_comm _ _
    have h : H.Adj (f x).val (e y) ↔
        (if crossC then
          x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y) :=
      hSym.trans ((hCrossAdj y x).trans (hReverse x y))
    simpa [J,phi] using h
  exact ⟨topC,crossC,
    rookDouble_graph_eq_of_layer_data J topC crossC hBB hTT hBT hTB⟩

end EPPAIII.BlockSystems
