import EPPAIII.BlockSystems.SmallHostRankThreeFinal

/-!
# Exact clique / independent / rank-three formulation

The preceding theorem proves the mathematical ordered-pair orbit
property for every host with the source hypotheses. Here we record the
standard rank-three classification wording in a separate definition:
the action is vertex-transitive, both non-diagonal adjacency statuses
occur, and each status is exactly one orbit.

This lets us state the precise disjunction in Proposition prop:rank3,
including complete and edgeless degenerate cases.
-/

namespace EPPAIII.BlockSystems

/-- The rank-three action property of an actual finite graph:
the diagonal is one orbit by transitivity, and the ordered edges
and ordered distinct nonedges are the two other orbits. -/
def HasRankThreeAutAction {W : Type*} (H : SimpleGraph W) : Prop :=
  (∃ u v : W, H.Adj u v) ∧
  (∃ u v : W, u ≠ v ∧ ¬ H.Adj u v) ∧
  EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H ∧
  HasOrderedPairOrbitByStatus H

/-- The paper's source-facing trichotomy, without assumptions on
which of the edge/nonedge pair types are nonempty. -/
theorem transitive_eppa_at_most_double_clique_empty_or_rank_three
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hPrimitiveIfDouble :
      Fintype.card W = 2 * Fintype.card V →
        IsPrimitiveAutAction H) :
    H = ⊤ ∨ H = ⊥ ∨ HasRankThreeAutAction H := by
  have hPairs : HasOrderedPairOrbitByStatus H :=
    transitive_eppa_at_most_double_has_pair_orbits
      G H e heppa hTrans hBound hPrimitiveIfDouble
  by_cases hEdge : ∃ u v : W, H.Adj u v
  · by_cases hNonedge :
        ∃ u v : W, u ≠ v ∧ ¬ H.Adj u v
    · exact Or.inr (Or.inr ⟨hEdge,hNonedge,hTrans,hPairs⟩)
    · left
      apply SimpleGraph.ext
      funext u v
      change H.Adj u v ↔ u ≠ v
      constructor
      · exact H.ne_of_adj
      · intro huv
        by_contra hNot
        exact hNonedge ⟨u,v,huv,hNot⟩
  · right
    left
    apply SimpleGraph.ext
    funext u v
    change H.Adj u v ↔ False
    exact ⟨fun h => hEdge ⟨u,v,h⟩, False.elim⟩

end EPPAIII.BlockSystems
