import EPPAIII.TwoGraphs.TripleParity
import EPPAIII.TwoGraphs.TaylorAutomorphismLift
import EPPAIII.DoubleCover.InducedTwoTransitiveAssembly
import EPPAIII.TwoGraphs.TaylorFibreRigidity

/-!
# Exact automorphism group of the two-graph induced by a Taylor double

Under invariance of its natural two-point fibres, an automorphism
of the Taylor double induces precisely an automorphism of the
odd-triple two-graph. Conversely any automorphism of the two-graph
lifts by the explicit XOR switching potential.

Combining the genuine EPPA pair-orbit theorem and
non-homogeneity yields 2-transitivity of this group. The final
source-facing theorem obtains fibre invariance from the merged
true-twin quotient proof; no extra orbit or classification axiom.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover
open EPPAIII.CliqueCovers

/-- The natural permutation group of odd-edge-parity triples.
Repeated indices automatically have false triple parity. -/
def IsTwoGraphAutomorphism {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Equiv.Perm V) : Prop :=
  ∀ x y z : V,
    OddBaseTriple G x y z ↔
      OddBaseTriple G (f x) (f y) (f z)

theorem oddBaseTriple_repeated_false {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V)
    (hRepeated : x = y ∨ y = z ∨ z = x) :
    ¬ OddBaseTriple G x y z := by
  have hSym : ∀ u v : V,
      decide (G.Adj u v) = decide (G.Adj v u) := by
    intro u v
    by_cases h : G.Adj u v
    · have hr := (G.adj_comm u v).mp h
      simp [h,hr]
    · have hr : ¬ G.Adj v u :=
        fun hv => h ((G.adj_comm u v).mpr hv)
      simp [h,hr]
  rcases hRepeated with hEq | hEq | hEq
  · subst y
    unfold OddBaseTriple
    rw [hSym z x]
    by_cases h : G.Adj x z <;> simp [h]
  · subst z
    unfold OddBaseTriple
    rw [hSym y x]
    by_cases h : G.Adj x y <;> simp [h]
  · subst z
    unfold OddBaseTriple
    rw [hSym y x]
    by_cases h : G.Adj x y <;> simp [h]

/-- Any genuine induced fibre action of a Taylor host preserves
the usual odd-triple two-graph, including repeated-index cases. -/
theorem induced_taylor_action_preserves_two_graph {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : InducedFibreAut (taylorPairGraph G)) :
    IsTwoGraphAutomorphism G A.σ := by
  intro x y z
  by_cases hxy : x = y
  · subst y
    have hFirst :
        ¬ OddBaseTriple G x x z :=
      oddBaseTriple_repeated_false G x x z (Or.inl rfl)
    have hSecond :
        ¬ OddBaseTriple G (A.σ x) (A.σ x) (A.σ z) :=
      oddBaseTriple_repeated_false G _ _ _ (Or.inl rfl)
    exact ⟨fun h => False.elim (hFirst h),
      fun h => False.elim (hSecond h)⟩
  by_cases hyz : y = z
  · subst z
    have hFirst :
        ¬ OddBaseTriple G x y y :=
      oddBaseTriple_repeated_false G x y y (Or.inr (Or.inl rfl))
    have hSecond :
        ¬ OddBaseTriple G (A.σ x) (A.σ y) (A.σ y) :=
      oddBaseTriple_repeated_false G _ _ _ (Or.inr (Or.inl rfl))
    exact ⟨fun h => False.elim (hFirst h),
      fun h => False.elim (hSecond h)⟩
  by_cases hzx : z = x
  · subst z
    have hFirst :
        ¬ OddBaseTriple G x y x :=
      oddBaseTriple_repeated_false G x y x (Or.inr (Or.inr rfl))
    have hSecond :
        ¬ OddBaseTriple G (A.σ x) (A.σ y) (A.σ x) :=
      oddBaseTriple_repeated_false G _ _ _ (Or.inr (Or.inr rfl))
    exact ⟨fun h => False.elim (hFirst h),
      fun h => False.elim (hSecond h)⟩
  exact oddBaseTriple_preserved_by_induced_action
    G A x y z hxy hyz hzx

/-- The induced base permutation of any fibre-preserving Taylor
graph automorphism belongs to the two-graph automorphism group. -/
theorem taylor_host_action_inside_two_graph {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (q : Equiv.Perm (Bool × V))
    (hq : EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q) :
    ∃ σ : Equiv.Perm V,
      IsTwoGraphAutomorphism G σ ∧
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) := by
  obtain ⟨σ,hσ⟩ := hPairs q hq
  let A : InducedFibreAut (taylorPairGraph G) :=
    ⟨q,σ,hq,hσ⟩
  exact ⟨σ,induced_taylor_action_preserves_two_graph G A,hσ⟩

private theorem bool_eq_of_true_iff (a b : Bool)
    (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- Every ordinary two-graph automorphism lifts to a Taylor host
automorphism. Its second coordinate is exactly the given f. -/
theorem two_graph_automorphism_lifts_to_taylor {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Equiv.Perm V)
    (hF : IsTwoGraphAutomorphism G f) :
    ∃ q : Equiv.Perm (Bool × V),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = f x) := by
  have hTriples : ∀ x y z : V,
      Bool.xor (Bool.xor (decide (G.Adj x y))
        (decide (G.Adj y z))) (decide (G.Adj z x)) =
      Bool.xor (Bool.xor (decide (G.Adj (f x) (f y)))
        (decide (G.Adj (f y) (f z))))
        (decide (G.Adj (f z) (f x))) := by
    intro x y z
    exact bool_eq_of_true_iff _ _ (hF x y z)
  obtain ⟨h,hAut,hBase⟩ :=
    taylor_automorphism_lift_of_triple_parity G f hTriples
  exact ⟨taylorSwitchLift f h,hAut,hBase⟩

/-- Exact equality of the induced permutation group with the
two-graph automorphism group, conditional only on invariance of
the natural fibres. -/
theorem taylor_induced_group_eq_two_graph {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hPairs : HasInvariantPairs (taylorPairGraph G)) :
    (∀ (q : Equiv.Perm (Bool × V)),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q →
      ∃ σ : Equiv.Perm V, IsTwoGraphAutomorphism G σ ∧
        (∀ b x, (q (b,x)).2 = σ x)) ∧
    (∀ σ : Equiv.Perm V, IsTwoGraphAutomorphism G σ →
      ∃ q : Equiv.Perm (Bool × V),
        EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
        (∀ b x, (q (b,x)).2 = σ x)) := by
  constructor
  · exact taylor_host_action_inside_two_graph G hPairs
  · exact two_graph_automorphism_lifts_to_taylor G

/-- EPPA and non-homogeneity imply 2-transitivity of the
associated two-graph automorphism group, once host fibre
invariance is established. -/
theorem taylor_eppa_two_graph_two_transitive_of_pairs {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heppa : IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ σ : Equiv.Perm V,
      IsTwoGraphAutomorphism G σ ∧ σ x = u ∧ σ y = v := by
  obtain ⟨A,hX,hY⟩ :=
    eppa_induced_fibre_action_two_transitive
      G (taylorPairGraph G) heppa hPairs
      hNonhomogeneous x y u v hxy huv
  exact ⟨A.σ,induced_taylor_action_preserves_two_graph G A,hX,hY⟩

end EPPAIII.TwoGraphs
