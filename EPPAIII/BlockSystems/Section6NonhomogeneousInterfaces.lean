import EPPAIII.BlockSystems.TransitiveClusterHomogeneity
import EPPAIII.CliqueCovers.NonclusterAllParameters
import EPPAIII.BlockSystems.UnequalNamedActualHost

/-!
# Section 6 classification with the manuscript's host hypotheses

The independently formalized equal-clique and unequal-clique host
classifications assume that H is not a union of cliques. The
manuscript's corresponding statements instead assume that the
vertex-transitive host H is non-homogeneous.

The missing implication is now proved in
TransitiveClusterHomogeneity.lean. This file applies it to the
existing classifications without assuming the structure of the
complementary half, a labelled outside copy, or coherent EPPA
extensions.

The external Gardiner and rank-three classifications needed by
other branches of the final imprimitive proposition are not part
of these theorems.
-/

namespace EPPAIII.CliqueCovers

/-- Equal-clique classification for a genuinely non-homogeneous
vertex-transitive host, with NO assumption that the outside half
induces another union of equal cliques.

This closes the exact classification interface missing between
the printed Lemma 6.1 and its use in Proposition 6.17. -/
theorem eppa_nonhomogeneous_clique_double_all_positive
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph H) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y) ∨
    (∃ (hS : s = 2) (hT : t = 2)
        (phi : CoverVertex 2 2 ≃ W),
       (∀ x : Fin 2 × Fin 2,
          phi (false,x) =
            e (Fin.cast hS.symm x.1, Fin.cast hT.symm x.2)) ∧
       H.comap phi = wagnerCanonicalGraph) := by
  exact eppa_noncluster_clique_double_all_positive
    H e heppa hs ht hOrder hTransitive
    (EPPAIII.BlockSystems.transitive_nonhomogeneous_not_cluster
      H hTransitive hNonhomogeneous)

end EPPAIII.CliqueCovers

namespace EPPAIII.BlockSystems

/-- Named unequal-clique EPPA host for the source-facing
non-homogeneous transitive case. Under the precise imprimitive
block and unequal component hypotheses, the host must be two
complete graphs joined by a perfect matching, with the base
embedding fixed by the relabelling. -/
theorem transitive_eppa_unequal_two_cliques_named_host_nonhomogeneous
    {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonhomogeneous : ¬ DoubleCover.IsHomogeneousGraph H)
    (hCluster : IsClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    ∃ (c : V → Bool) (φ : Bool × V ≃ W),
      G = twoCliqueGraph c ∧
      (∀ v : V, φ (false,v) = e v) ∧
      pullbackGraph H φ = twoCliqueMatchedGraph c true := by
  have hTransitive : CliqueCovers.HasTransitiveGraphAutomorphisms H :=
    hTrans
  have hNonCluster : ¬ IsClusterGraph H :=
    transitive_nonhomogeneous_not_cluster H hTransitive hNonhomogeneous
  exact transitive_eppa_unequal_two_cliques_named_host
    G H e heppa block hBlocks hSurj hTrans
    hNonCluster hCluster hManyBlocks hNontrivial
    hHostSize x y hDifferent

end EPPAIII.BlockSystems
