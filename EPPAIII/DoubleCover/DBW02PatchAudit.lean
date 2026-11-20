import EPPAIII.DoubleCover.InterblockOrbits

/-!
# DBW-02: source-ordered validation of Claims 5.14–5.15

This is a regression certificate for the short November 20 paper repair.
It makes the dependencies visible and avoids using the final assembled
imprimitive-classification theorem as a substitute for the argument:
- true EPPA and an invariant two-point fibre system;
- uniform inter-fibre pair matrices;
- equal numbers of edges of both base adjacency types;
- elimination of the one-edge and three-edge patterns;
- the Taylor pattern, its deck involution, and ordered inter-fibre orbits.

The preceding manuscript supplies the invariant fibre system and
non-homogeneity.  Neither coherent extensions nor external Gardiner
classification are assumed in this theorem.
-/

namespace EPPAIII.DoubleCover

theorem dbw02_claim514_515_canonical_audit {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    RepresentsPairPattern G H taylor ∧
    IsGraphAutomorphism H (deckSwap V) ∧
    (∀ x y z w : V, x ≠ y → z ≠ w →
      FibrePairReach H x y z w) ∧
    (∀ (b c d e : Bool) (x y z w : V),
      x ≠ y → z ≠ w →
      (H.Adj (b, x) (c, y) ↔ H.Adj (d, z) (e, w)) →
      ∃ q : Equiv.Perm (Bool × V),
        IsGraphAutomorphism H q ∧
        q (b, x) = (d, z) ∧ q (c, y) = (e, w)) := by
  classical
  obtain ⟨xe, ye, xn, yn, hEdge, hDistinct, hNonedge⟩ :=
    edge_and_nonedge_of_nonhomogeneous G hNonHomogeneous
  obtain ⟨p, hp⟩ :=
    eppa_has_uniform_pair_pattern G H heppa hPairs
      xe ye xn yn hEdge hDistinct hNonedge
  have hEqualCount : p.edgeCount = p.nonedgeCount :=
    balanced_of_nonhomogeneous G H heppa hPairs p hp hNonHomogeneous
  have hTaylor : p = taylor := by
    rcases nonhomogeneous_pair_pattern_cases
      G H heppa hPairs p hp hNonHomogeneous with hOne | hTwo | hThree
    · subst p
      exact False.elim (hNonHomogeneous
        (oneEdge_forces_homogeneous G H heppa hPairs hp))
    · exact hTwo
    · subst p
      exact False.elim (hNonHomogeneous
        (threeEdges_forces_homogeneous G H heppa hPairs hp))
  have hRep : RepresentsPairPattern G H taylor := hTaylor ▸ hp
  have hDeck : IsGraphAutomorphism H (deckSwap V) :=
    deckSwap_graph_automorphism G H heppa.1 hRep
  refine ⟨hRep, hDeck, ?_, ?_⟩
  · intro x y z w hxy hzw
    exact eppa_fibre_action_two_transitive
      G H heppa hPairs hNonHomogeneous x y z w hxy hzw
  · intro b c d e x y z w hxy hzw hStatus
    exact eppa_interfibre_pair_status_transitive
      G H heppa hPairs hNonHomogeneous
      b c d e x y z w hxy hzw hStatus

end EPPAIII.DoubleCover
