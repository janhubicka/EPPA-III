import EPPAIII.BlockSystems.GraphTransport

/-!
# From a transitive imprimitivity system to a Taylor double

This closes the structural implication of Lemma 3.3 without assuming
the host is already presented as Bool × V.

The inputs express:
* a genuine fixed EPPA embedding e : G ↪ H;
* vertex-transitivity of H and an Aut(H)-invariant nontrivial partition;
* |H| = 2|G|;
* non-homogeneity of G and exclusion of unions of cliques and their
  complements.

Claim 3.4 supplies the two-point block system; CanonicalPairs constructs
a genuine equivalence φ : Bool × V ≃ W; GraphTransport carries EPPA
and block invariance across φ; CompleteTaylor forces the Taylor
inter-fibre structure with optional matching of mates.

This is the structural half of Lemma 3.3. The additional assertion
about transitivity on ordered inter-block edges and nonedges is not
included here and remains an explicit separate obligation.
-/

namespace EPPAIII.BlockSystems

/-- Structural Taylor-double conclusion, starting from the actual
vertex set of an arbitrary finite EPPA host. The equivalence and
mate-matching bit are *produced*, not postulated. -/
theorem transitive_eppa_double_cover_up_to_mate {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    ∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      ∃ mate : Bool,
        (∀ x : V, H.Adj (φ (false,x)) (φ (true,x)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern
          G (pullbackGraph H φ) DoubleCover.taylor := by
  classical
  obtain ⟨hInject, _hCount, hTwo⟩ :=
    transitive_eppa_blocks_are_pairs G H e heppa block
      hTrans hBlocks hSurj hNonHomogeneous
      hNonCluster hNonCoCluster hManyBlocks
      hNontrivial hHostSize
  obtain ⟨φ, hBottom, hPairBlock⟩ :=
    exists_canonical_pair_equiv e block hInject hTwo hHostSize
  have heppa' : IsEPPAEmbedding
      G (pullbackGraph H φ) (DoubleCover.bottomEmbedding V) :=
    eppa_pullback_bottom G H e heppa φ hBottom
  have hPairs' : DoubleCover.HasInvariantPairs (pullbackGraph H φ) :=
    invariant_pairs_of_pullback H e block hBlocks hInject φ hPairBlock
  obtain ⟨mate, hMate, hInter⟩ :=
    DoubleCover.eppa_taylor_double_up_to_mate
      G (pullbackGraph H φ) heppa' hPairs' hNonHomogeneous
  refine ⟨φ, hBottom, mate, ?_, hInter⟩
  intro x
  exact hMate x

end EPPAIII.BlockSystems
