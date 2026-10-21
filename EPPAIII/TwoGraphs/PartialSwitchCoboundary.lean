import EPPAIII.TwoGraphs.OneForAll
import EPPAIII.TwoGraphs.XorSwitchingPotential
import EPPAIII.TwoGraphs.TransversalParity

/-!
# Linear-algebraic reduction of the partial two-graph switching lemma

For a partial two-graph automorphism p with finite domain D,
the discrepancy between the base adjacency on x,y and p(x),p(y)
is an XOR coboundary h(x) XOR h(y), defined on all of V.

To make p preserve a switched graph, it is sufficient to
find a Boolean side function t and one global bit c satisfying
  t(x) XOR t(p(x)) = h(x) XOR c
for each x in D. This identifies the precise remaining
path/cycle compatibility problem. No existence of t or c is
assumed by the final lemma; it is isolated as a separate
explicit hypothesis until the cyclic induction is validated.
-/

namespace EPPAIII.TwoGraphs

private theorem bool_eq_of_true_iff_partial
    (a b : Bool) (h : (a = true ↔ b = true)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The edge discrepancy of any partial two-graph
automorphism is a one-vertex XOR coboundary on its domain.
The potential is extended arbitrarily (by false) outside D. -/
theorem partial_two_graph_discrepancy_potential
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V)
    (hp : IsPartialTwoGraphAutomorphism G D p) :
    ∃ h : V → Bool,
      ∀ x ∈ D, ∀ y ∈ D,
        Bool.xor (decide (G.Adj x y))
          (decide (G.Adj (p x) (p y))) =
            Bool.xor (h x) (h y) := by
  classical
  let edge : V → V → Bool := fun x y => decide (G.Adj x y)
  have hEdgeSym : ∀ x y : V, edge x y = edge y x := by
    intro x y
    by_cases hx : G.Adj x y
    · have hy : G.Adj y x := (G.adj_comm x y).mp hx
      simp [edge,hx,hy]
    · have hy : ¬ G.Adj y x :=
        fun hh => hx ((G.adj_comm x y).mpr hh)
      simp [edge,hx,hy]
  let Sub := {x : V // x ∈ D}
  let delta : Sub → Sub → Bool := fun x y =>
    Bool.xor (edge x.1 y.1) (edge (p x.1) (p y.1))
  have hDeltaSym : ∀ x y : Sub, delta x y = delta y x := by
    intro x y
    dsimp [delta]
    rw [hEdgeSym x.1 y.1, hEdgeSym (p x.1) (p y.1)]
  have hTriple : ∀ x y z : Sub,
      Bool.xor (Bool.xor (edge x.1 y.1) (edge y.1 z.1))
        (edge z.1 x.1) =
      Bool.xor (Bool.xor (edge (p x.1) (p y.1))
        (edge (p y.1) (p z.1))) (edge (p z.1) (p x.1)) := by
    intro x y z
    exact bool_eq_of_true_iff_partial _ _
      (hp x.1 x.2 y.1 y.2 z.1 z.2)
  have hTriangle : ∀ x y z : Sub,
      Bool.xor (Bool.xor (delta x y) (delta y z))
        (delta z x) = false := by
    intro x y z
    dsimp [delta]
    exact xor_three_pairs_zero
      (edge x.1 y.1) (edge y.1 z.1) (edge z.1 x.1)
      (edge (p x.1) (p y.1))
      (edge (p y.1) (p z.1))
      (edge (p z.1) (p x.1)) (hTriple x y z)
  obtain ⟨h,hDelta⟩ :=
    xor_triangle_potential delta hDeltaSym hTriangle
  let hFull : V → Bool := fun x =>
    if hx : x ∈ D then h ⟨x,hx⟩ else false
  refine ⟨hFull, ?_⟩
  intro x hx y hy
  have hd := hDelta ⟨x,hx⟩ ⟨y,hy⟩
  change Bool.xor (edge x y) (edge (p x) (p y)) =
    Bool.xor (h ⟨x,hx⟩) (h ⟨y,hy⟩) at hd
  simpa [hFull,edge,hx,hy] using hd

/-- The nine-Boolean-variable identity underlying the
switching equations. Two appearances of the global c cancel. -/
private theorem xor_switch_compatibility
    (a b hx hy tx ty ux uy c : Bool)
    (hDelta : Bool.xor a b = Bool.xor hx hy)
    (hX : Bool.xor tx ux = Bool.xor hx c)
    (hY : Bool.xor ty uy = Bool.xor hy c) :
    Bool.xor a (Bool.xor tx ty) =
      Bool.xor b (Bool.xor ux uy) := by
  cases a <;> cases b <;>
    cases hx <;> cases hy <;>
    cases tx <;> cases ty <;>
    cases ux <;> cases uy <;>
    cases c <;> simp_all [Bool.xor]

/-- Decidable adjacency is equivalent precisely when its
Boolean decisions agree. -/
private theorem iff_of_decide_eq
    (P Q : Prop) [Decidable P] [Decidable Q]
    (h : decide P = decide Q) : P ↔ Q := by
  by_cases hp : P <;> by_cases hq : Q <;> simp_all

/-- Once the vertex equations have been solved, the partial
two-graph map is a partial graph automorphism of the switched
representative. This theorem is independent of how the solution
is constructed (paths, cycles, or linear algebra). -/
theorem partial_switch_of_vertex_equations
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (p : Equiv.Perm V)
    (h t : V → Bool) (c : Bool)
    (hDelta : ∀ x ∈ D, ∀ y ∈ D,
      Bool.xor (decide (G.Adj x y))
        (decide (G.Adj (p x) (p y))) =
          Bool.xor (h x) (h y))
    (hVertex : ∀ x ∈ D,
      Bool.xor (t x) (t (p x)) = Bool.xor (h x) c) :
    EPPAIII.IsPartialGraphAutomorphism
      (taylorTransversalGraph G t) D p := by
  classical
  intro x y hx hy
  have hDecision :
      decide ((taylorTransversalGraph G t).Adj x y) =
        decide ((taylorTransversalGraph G t).Adj (p x) (p y)) := by
    calc
      decide ((taylorTransversalGraph G t).Adj x y) =
        Bool.xor (decide (G.Adj x y)) (Bool.xor (t x) (t y)) :=
          taylor_transversal_decide_adj G t x y
      _ = Bool.xor (decide (G.Adj (p x) (p y)))
            (Bool.xor (t (p x)) (t (p y))) :=
        xor_switch_compatibility
          (decide (G.Adj x y)) (decide (G.Adj (p x) (p y)))
          (h x) (h y) (t x) (t y) (t (p x)) (t (p y)) c
          (hDelta x hx y hy) (hVertex x hx) (hVertex y hy)
      _ = decide ((taylorTransversalGraph G t).Adj (p x) (p y)) :=
        (taylor_transversal_decide_adj G t (p x) (p y)).symm
  exact iff_of_decide_eq _ _ hDecision

end EPPAIII.TwoGraphs
