import EPPAIII.EPPA.PartialSwap
import EPPAIII.TwoGraphs.OnePointParity
import EPPAIII.TwoGraphs.Separation

/-!
# Pointwise extension of equal neighbourhood types

An elementary partial-swap lemma constructs a genuine partial graph
automorphism which fixes a finite set and sends a to b whenever
their adjacency types agree into that set. EPPA then extends the
partial swap to a host automorphism. Fibre invariance descends it
to the associated two-graph, fixing the whole finite set pointwise.

The complementary-type case will use the previously verified
separating EPPA transversal.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- This partial-swap lemma was first used for two-graph automorphisms. -/
alias equal_types_partial_swap := EPPAIII.equal_types_partial_swap

/-- If a and b have equal graph adjacency types into R, an
actual EPPA Taylor double with invariant fibres supplies a
two-graph automorphism sending a to b and fixing R pointwise. -/
theorem eppa_one_point_extension_equal_types
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (R : Finset V) (a b : V)
    (ha : a ∉ R) (hb : b ∉ R)
    (hEqual : ∀ r ∈ R, G.Adj a r ↔ G.Adj b r) :
    ∃ σ : Equiv.Perm V,
      IsTwoGraphAutomorphism G σ ∧ σ a = b ∧
      (∀ r ∈ R, σ r = r) := by
  classical
  let p : Equiv.Perm V := Equiv.swap a b
  have hPartial : EPPAIII.IsPartialGraphAutomorphism
      G (insert a R) p :=
    equal_types_partial_swap G R a b ha hb hEqual
  obtain ⟨q,hq,hExtend⟩ := heppa.2 (insert a R) p hPartial
  obtain ⟨σ,hσTwo,hBase⟩ :=
    taylor_host_action_inside_two_graph G hPairs q hq
  refine ⟨σ,hσTwo,?_,?_⟩
  · have hh := hExtend a (by simp)
    change q (false,a) = (false,p a) at hh
    have h := congrArg Prod.snd hh
    simpa [p] using (hBase false a).symm.trans h
  · intro r hr
    have hFix : p r = r := by
      have hra : r ≠ a := by
        intro hh; exact ha (hh ▸ hr)
      have hrb : r ≠ b := by
        intro hh; exact hb (hh ▸ hr)
      exact Equiv.swap_apply_of_ne_of_ne hra hrb
    have hh := hExtend r (Finset.mem_insert_of_mem hr)
    change q (false,r) = (false,p r) at hh
    have h := congrArg Prod.snd hh
    simpa [hFix] using (hBase false r).symm.trans h

end EPPAIII.TwoGraphs
