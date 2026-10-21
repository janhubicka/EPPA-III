import EPPAIII.TwoGraphs.TrivialTwoGraph

/-!
# Triple parity on every transversal of the Taylor double

A transversal chosen by t : V -> Bool induces the switching of G
at t. Pair adjacencies change by t(x) XOR t(y); their sum on
a triple is unchanged. Hence a partial automorphism of any
transversal graph is automatically a partial automorphism of the
associated two-graph. This is the input for the full switching-
class consequence of Proposition 5.11.
-/

namespace EPPAIII.TwoGraphs

/-- Select one vertex from each canonical Taylor fibre. -/
def taylorTransversalEmbedding {V : Type*}
    (t : V → Bool) : V ↪ Bool × V where
  toFun := fun x => (t x,x)
  inj' := by
    intro x y h
    exact congrArg Prod.snd h

/-- The induced switching representative on the selected transversal. -/
def taylorTransversalGraph {V : Type*}
    (G : SimpleGraph V) (t : V → Bool) : SimpleGraph V :=
  (taylorPairGraph G).comap (taylorTransversalEmbedding t)

/-- Pair adjacency is toggled exactly when the two chosen
side bits differ. This includes the diagonal x=y. -/
theorem taylor_transversal_decide_adj
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → Bool) (x y : V) :
    decide ((taylorTransversalGraph G t).Adj x y) =
      Bool.xor (decide (G.Adj x y)) (Bool.xor (t x) (t y)) := by
  classical
  by_cases hxy : x = y
  · subst y
    have hn : ¬ G.Adj x x := fun h => (G.ne_of_adj h) rfl
    simp [taylorTransversalGraph,taylorTransversalEmbedding,
      taylorPairGraph,taylorPairAdj,hn,Bool.xor]
  · change decide (x ≠ y ∧ (G.Adj x y ↔ t x = t y)) =
      Bool.xor (decide (G.Adj x y)) (Bool.xor (t x) (t y))
    cases htx : t x <;> cases hty : t y <;>
      by_cases hg : G.Adj x y <;>
      simp_all [Bool.xor]

/-- Every switching edge discrepancy appears twice in the parity
of a triple and therefore cancels. -/
private theorem xor_triple_switch_invariant
    (a b c p q r : Bool) :
    Bool.xor (Bool.xor
      (Bool.xor a (Bool.xor p q))
      (Bool.xor b (Bool.xor q r)))
      (Bool.xor c (Bool.xor r p)) =
    Bool.xor (Bool.xor a b) c := by
  cases a <;> cases b <;> cases c <;>
    cases p <;> cases q <;> cases r <;> rfl

/-- The usual odd-parity two-graph is unchanged by *any*
choice of the canonical Taylor transversal. Repetitions
of vertices are covered, not silently excluded. -/
theorem odd_triple_transversal_iff
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → Bool) (x y z : V) :
    OddBaseTriple (taylorTransversalGraph G t) x y z ↔
      OddBaseTriple G x y z := by
  classical
  unfold OddBaseTriple
  rw [taylor_transversal_decide_adj G t x y,
      taylor_transversal_decide_adj G t y z,
      taylor_transversal_decide_adj G t z x]
  rw [xor_triple_switch_invariant]

/-- A genuine partial graph automorphism of a chosen transversal
preserves every odd-parity triple of the underlying two-graph. -/
theorem partial_transversal_preserves_two_graph
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : V → Bool)
    (D : Finset V) (p : Equiv.Perm V)
    (hp : EPPAIII.IsPartialGraphAutomorphism
      (taylorTransversalGraph G t) D p) :
    IsPartialTwoGraphAutomorphism G D p := by
  classical
  let C := taylorTransversalGraph G t
  intro x hx y hy z hz
  have hDecide (u v : V) (hu : u ∈ D) (hv : v ∈ D) :
      decide (C.Adj u v) = decide (C.Adj (p u) (p v)) := by
    by_cases h : C.Adj u v
    · have hh := (hp u v hu hv).mp h
      simp [h,hh]
    · have hh : ¬ C.Adj (p u) (p v) :=
        fun he => h ((hp u v hu hv).mpr he)
      simp [h,hh]
  have hC : OddBaseTriple C x y z ↔
      OddBaseTriple C (p x) (p y) (p z) := by
    unfold OddBaseTriple
    rw [hDecide x y hx hy, hDecide y z hy hz, hDecide z x hz hx]
  exact (odd_triple_transversal_iff G t x y z).symm.trans
    (hC.trans (odd_triple_transversal_iff G t (p x) (p y) (p z)))

end EPPAIII.TwoGraphs
