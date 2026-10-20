import EPPAIII.TwoGraphs.TaylorEvenTripleCoverage
import EPPAIII.TwoGraphs.TaylorIntrinsicFibreAction

/-!
# Fibre rigidity for an actual EPPA Taylor double

Combine the fully certified true-twin quotient contradiction with
the elementary intrinsic distance-three characterization of mates.

The result is the source-facing fibre-invariance conclusion of
Section 5, conditional only on:
* an actual EPPA embedding of G into its canonical Taylor double;
* non-homogeneity of G;
* existence of at least one even-parity base triple.

The latter is the nontriviality condition for the associated
two-graph. No classification input or coherent extension is used.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- Full fibre-rigidity conclusion of the imprimitive Section 5:
every host automorphism induces a permutation on the natural
two-point fibres of the Taylor double. -/
theorem taylor_eppa_intrinsic_fibres
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G (taylorPairGraph G)
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph G)
    (hEven : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      EvenTriple G a b c) :
    EPPAIII.DoubleCover.HasInvariantPairs (taylorPairGraph G) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,hTriple⟩ := hEven
  haveI : Nontrivial V := ⟨⟨a,b,hab⟩⟩
  apply taylor_invariant_pairs_of_even_coverage G
  exact taylor_eppa_even_triple_pair_coverage
    G heppa ⟨a,b,c,hab,hac,hbc,hTriple⟩ hNonhomogeneous

end EPPAIII.TwoGraphs
