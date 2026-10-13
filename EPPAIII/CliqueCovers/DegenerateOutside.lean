import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.CliqueCovers.SpanningEdgeRigidity

/-!
# Degenerate parameters in the complementary-half partition lemma

For a vertex-transitive graph H with 2st vertices containing an
induced sK_t, its complementary half has the same internal edge
count. At s=1 this is the maximal count on t vertices, so the
complementary half is K_t. At t=1 it is zero, hence the
complementary half is an independent s-set.

The proofs use an actual equivalence between the complementary
half and Fin s × Fin t supplied by the exact vertex count. Thus
they discharge the s=1 and t=1 cases of the complementary-half
partition lemma without assuming any outside clique partition,
EPPA, or a particular host vertex type.
-/

namespace EPPAIII.CliqueCovers

/-- A single clique K_t, represented by 1K_t, is the complete
graph on Fin 1 × Fin t. -/
theorem cliqueUnion_one_left_eq_top (t : ℕ) :
    cliqueUnion 1 t = (⊤ : SimpleGraph (Fin 1 × Fin t)) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔ x ≠ y
  have hFirst : x.1 = y.1 := Subsingleton.elim _ _
  constructor
  · intro hxy hEq
    exact hxy.2 (congrArg Prod.snd hEq)
  · intro hxy
    refine ⟨hFirst, ?_⟩
    intro hSecond
    exact hxy (Prod.ext hFirst hSecond)

/-- The graph sK_1 has no edges. -/
theorem cliqueUnion_one_right_eq_bot (s : ℕ) :
    cliqueUnion s 1 = (⊥ : SimpleGraph (Fin s × Fin 1)) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔ False
  constructor
  · intro hxy
    exact hxy.2 (Subsingleton.elim _ _)
  · intro h
    exact False.elim h

/-- The exact order 2st makes the outside subtype equivalent to
the selected vertex type, without any preselected partition. -/
noncomputable def balancedOutsideEquiv {s t : ℕ}
    {W : Type*} [Fintype W]
    (e : (Fin s × Fin t) ↪ W)
    (hOrder : Fintype.card W = 2 * s * t) :
    (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e} := by
  classical
  apply Fintype.equivOfCardEq
  calc
    Fintype.card (Fin s × Fin t) = s * t := by simp
    _ = (finiteOutside e).card :=
      (finiteOutside_card_clique_union e hOrder).symm
    _ = Fintype.card {u : W // u ∈ finiteOutside e} := by
      simp only [Fintype.card_coe]

/-- Equality of edge counts with 1K_t makes any graph on its
vertex set equal to the complete graph. -/
theorem graph_eq_cliqueUnion_one_left_of_edge_count
    (t : ℕ) (B : SimpleGraph (Fin 1 × Fin t))
    [DecidableRel B.Adj]
    (hEdges : B.edgeSet.ncard = (cliqueUnion 1 t).edgeSet.ncard) :
    B = cliqueUnion 1 t := by
  classical
  have hSub : B ≤ cliqueUnion 1 t := by
    rw [cliqueUnion_one_left_eq_top]
    exact le_top
  have hCount : B.edgeFinset.card = (cliqueUnion 1 t).edgeFinset.card := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hEdges
  exact graph_eq_of_le_of_edge_card_eq B (cliqueUnion 1 t) hSub hCount

/-- Equal edge counts with sK_1 make any graph on its vertex
set empty. -/
theorem graph_eq_cliqueUnion_one_right_of_edge_count
    (s : ℕ) (B : SimpleGraph (Fin s × Fin 1))
    [DecidableRel B.Adj]
    (hEdges : B.edgeSet.ncard = (cliqueUnion s 1).edgeSet.ncard) :
    B = cliqueUnion s 1 := by
  classical
  have hSub : cliqueUnion s 1 ≤ B := by
    rw [cliqueUnion_one_right_eq_bot]
    exact bot_le
  have hCount : (cliqueUnion s 1).edgeFinset.card = B.edgeFinset.card := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hEdges.symm
  exact (graph_eq_of_le_of_edge_card_eq
    (cliqueUnion s 1) B hSub hCount).symm

/-- For any vertex-transitive double-sized host containing a
distinguished K_t, the outside half is also K_t. -/
theorem outside_of_transitive_one_clique {t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 1 × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion 1 t) H e)
    (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * 1 * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ label : (Fin 1 × Fin t) ≃ {u : W // u ∈ finiteOutside e},
      (outsideInducedGraph H e).comap label = cliqueUnion 1 t := by
  classical
  let label := balancedOutsideEquiv e hOrder
  letI : Nonempty (Fin 1 × Fin t) := ⟨(⟨0,by decide⟩,⟨0,ht⟩)⟩
  have hEdges :=
    arbitrary_host_outside_edge_count_eq_base
      (cliqueUnion 1 t) H e he label hTransitive
  refine ⟨label, ?_⟩
  exact graph_eq_cliqueUnion_one_left_of_edge_count
    t ((outsideInducedGraph H e).comap label) hEdges

/-- For any vertex-transitive double-sized host containing a
distinguished independent s-set, the outside half is also
independent. -/
theorem outside_of_transitive_one_vertex_cliques {s : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin 1) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s 1) H e)
    (hs : 0 < s)
    (hOrder : Fintype.card W = 2 * s * 1)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ label : (Fin s × Fin 1) ≃ {u : W // u ∈ finiteOutside e},
      (outsideInducedGraph H e).comap label = cliqueUnion s 1 := by
  classical
  let label := balancedOutsideEquiv e hOrder
  letI : Nonempty (Fin s × Fin 1) := ⟨(⟨0,hs⟩,⟨0,by decide⟩)⟩
  have hEdges :=
    arbitrary_host_outside_edge_count_eq_base
      (cliqueUnion s 1) H e he label hTransitive
  refine ⟨label, ?_⟩
  exact graph_eq_cliqueUnion_one_right_of_edge_count
    s ((outsideInducedGraph H e).comap label) hEdges

end EPPAIII.CliqueCovers
