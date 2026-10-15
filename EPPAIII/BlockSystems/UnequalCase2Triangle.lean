import EPPAIII.BlockSystems.UnequalCase2Taylor
import EPPAIII.DoubleCover.TaylorUnequalCliqueObstruction

/-!
# Unequal-clique Case 2: derive the triangle obstruction from actual EPPA

The previous theorems construct the canonical pair coordinates
directly from a nontrivial invariant block system in the genuine
double-sized EPPA host, and prove that the pulled-back host has
the Taylor inter-fibre matrix (possibly with mate edges).

Vertex transitivity is preserved by that bijective relabelling.
The now-verified exact Taylor triangle-count theorem eliminates the
case of unequal clique orders with a nonempty third component.
Neither a coherent system of EPPA lifts nor a prespecified second
half is assumed.
-/

namespace EPPAIII.BlockSystems

/-- Genuine host vertex transitivity transports along an arbitrary
equivalence of vertices. -/
theorem vertex_transitive_pullback {X W : Type*}
    (H : SimpleGraph W) (φ : X ≃ W)
    (hTrans : IsVertexTransitive H) :
    IsVertexTransitive (pullbackGraph H φ) := by
  intro a b
  obtain ⟨q,hq,hqa⟩ := hTrans (φ a) (φ b)
  let q' : Equiv.Perm X := (φ.trans q).trans φ.symm
  refine ⟨q',?_,?_⟩
  · intro u v
    change H.Adj (φ u) (φ v) ↔
      H.Adj (φ (q' u)) (φ (q' v))
    simpa [q'] using hq (φ u) (φ v)
  · apply φ.injective
    simpa [q'] using hqa

/-- In the crossing-edge Case 2 of the unequal-clique proof,
a non-homogeneous genuine double-size transitive EPPA host
cannot contain a third clique component if two component
orders differ. All pair-system and Taylor hypotheses are
deduced from the invariant partition and EPPA itself. -/
theorem transitive_eppa_case2_unequal_three_components_impossible
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hCluster : IsClusterGraph G)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ x y : V,
      G.Adj x y ∧ block (e x) ≠ block (e y))
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card)
    (hThird :
      (DoubleCover.clusterBaseNeighbours G x).card +
        (DoubleCover.clusterBaseNeighbours G y).card + 2 <
          Fintype.card V) : False := by
  obtain ⟨φ,hBottom,mate,hMate,hTaylor⟩ :=
    transitive_eppa_crossing_edge_taylor_up_to_mate
      G H e heppa block hBlocks hSurj hTrans
      hNonHomogeneous hCoP3 hCross hManyBlocks
      hNontrivial hHostSize
  have he' : IsInducedGraphEmbedding
      G (pullbackGraph H φ) (DoubleCover.bottomEmbedding V) :=
    (eppa_pullback_bottom G H e heppa φ hBottom).1
  have hTrans' : IsVertexTransitive (pullbackGraph H φ) :=
    vertex_transitive_pullback H φ hTrans
  exact DoubleCover.taylor_unequal_cliques_three_components_not_transitive
    G (pullbackGraph H φ) he' hTaylor hCluster
      hTrans' x y hDifferent hThird

end EPPAIII.BlockSystems
