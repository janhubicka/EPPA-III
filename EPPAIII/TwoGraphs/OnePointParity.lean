import EPPAIII.TwoGraphs.OneForAllParity
import EPPAIII.TwoGraphs.TaylorTwoGraphGroup

/-!
# The types of a one-point partial two-graph automorphism

If replacing one vertex a by b preserves the odd-parity relation
on all triples through a finite fixed set R, the two adjacency
types into R must either agree everywhere or disagree everywhere.

This is exactly the nontrivial local parity step in the
one-for-all proof, without assuming any group action or EPPA.
-/

namespace EPPAIII.TwoGraphs

private theorem boolean_eq_of_true_iff
    (u v : Bool) (h : (u = true ↔ v = true)) : u = v := by
  cases u <;> cases v <;> simp_all

private theorem xor_pair_types_of_same_triple_parity
    (ar as br bs rs : Bool)
    (h : Bool.xor (Bool.xor ar rs) as =
      Bool.xor (Bool.xor br rs) bs) :
    Bool.xor ar as = Bool.xor br bs := by
  cases ar <;> cases as <;> cases br <;>
    cases bs <;> cases rs <;> simp_all [Bool.xor]

private theorem decide_graph_adj_comm {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    decide (G.Adj x y) = decide (G.Adj y x) := by
  by_cases h : G.Adj x y
  · have hh := (G.adj_comm x y).mp h
    simp [h,hh]
  · have hh : ¬ G.Adj y x :=
      fun hy => h ((G.adj_comm x y).mpr hy)
    simp [h,hh]

/-- Parity preservation on triples (a,r,s) versus (b,r,s)
forces uniform equality or uniform complementation of the
adjacency types of a,b into R. The empty R case is included. -/
theorem one_point_two_graph_types_uniform
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (R : Finset V)
    (hParity : ∀ r ∈ R, ∀ s ∈ R,
      (OddBaseTriple G a r s ↔ OddBaseTriple G b r s)) :
    (∀ r ∈ R, G.Adj a r ↔ G.Adj b r) ∨
    (∀ r ∈ R, G.Adj a r ↔ ¬ G.Adj b r) := by
  let U := {r : V // r ∈ R}
  let ea : U → Bool := fun r => decide (G.Adj a r.1)
  let eb : U → Bool := fun r => decide (G.Adj b r.1)
  have hTypes : ∀ r s : U,
      Bool.xor (ea r) (ea s) = Bool.xor (eb r) (eb s) := by
    intro r s
    have ht := hParity r.1 r.2 s.1 s.2
    have hh := boolean_eq_of_true_iff _ _ ht
    unfold OddBaseTriple at hh
    rw [decide_graph_adj_comm G s.1 a,
        decide_graph_adj_comm G s.1 b] at hh
    exact xor_pair_types_of_same_triple_parity
      (ea r) (ea s) (eb r) (eb s) (decide (G.Adj r.1 s.1)) hh
  rcases types_equal_or_complementary ea eb hTypes with hEqual | hOpp
  · left
    intro r hr
    have hh := hEqual ⟨r,hr⟩
    change decide (G.Adj a r) = decide (G.Adj b r) at hh
    by_cases har : G.Adj a r <;> by_cases hbr : G.Adj b r <;>
      simp_all
  · right
    intro r hr
    have hh := hOpp ⟨r,hr⟩
    change decide (G.Adj a r) ≠ decide (G.Adj b r) at hh
    by_cases har : G.Adj a r <;> by_cases hbr : G.Adj b r <;>
      simp_all

end EPPAIII.TwoGraphs
