import EPPAIII.TwoGraphs.PartialAutomorphismParity

/-!
# Pair distances in a Taylor double

A graph-theoretic half of Section 5.1 fibre rigidity. We work with
the explicit Taylor relation on Bool × V and do not assume EPPA.

The missing separate input from the source proof is that for every
distinct base pair there is a third vertex forming an even-parity
triple. The results here characterize the short walks once that
condition holds. No distance or connectivity axiom is introduced.
-/

namespace EPPAIII.TwoGraphs

/-- Explicit Taylor adjacency: different base vertices, and
adjacency in the base exactly when the two side bits agree. -/
def taylorPairAdj {V : Type*} (G : SimpleGraph V)
    (u v : Bool × V) : Prop :=
  u.2 ≠ v.2 ∧ (G.Adj u.2 v.2 ↔ u.1 = v.1)

/-- The corresponding undirected graph on the two layers. -/
def taylorPairGraph {V : Type*} (G : SimpleGraph V) :
    SimpleGraph (Bool × V) where
  Adj := taylorPairAdj G
  symm := by
    constructor
    intro u v huv
    rcases huv with ⟨hxy,hAdj⟩
    refine ⟨hxy.symm, ?_⟩
    constructor
    · intro h
      exact ((hAdj.mp ((G.adj_comm _ _).mp h))).symm
    · intro h
      exact (G.adj_comm _ _).mpr (hAdj.mpr h.symm)
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- A triple has even base edge parity exactly when the
third base edge is the XOR of the other two. -/
def EvenTriple {V : Type*} (G : SimpleGraph V)
    (x y z : V) : Prop :=
  (G.Adj x y ↔ (G.Adj x z ↔ ¬ G.Adj y z))

/-- Two distinct lifts of the same base point are never adjacent. -/
theorem taylor_mates_not_adj {V : Type*} (G : SimpleGraph V)
    (b : Bool) (x : V) :
    ¬ (taylorPairGraph G).Adj (b,x) (!b,x) := by
  intro h
  exact h.1 rfl

/-- The two lifts of the same base vertex have no common neighbour.
Consequently they are never joined by a path of length one or two. -/
theorem taylor_mates_no_common_neighbour {V : Type*}
    (G : SimpleGraph V) (b : Bool) (x : V) :
    ¬ ∃ w : Bool × V,
      (taylorPairGraph G).Adj (b,x) w ∧
        (taylorPairGraph G).Adj (!b,x) w := by
  rintro ⟨⟨c,z⟩, h1, h2⟩
  rcases h1 with ⟨_, hb⟩
  rcases h2 with ⟨_, hc⟩
  have hh : (b = c) ↔ ((!b) = c) := hb.symm.trans hc
  cases b <;> cases c <;> simp at hh

/-- Nonadjacent vertices over distinct points are joined by a
two-edge path whenever those base points lie in an even triple. -/
theorem taylor_different_fibres_two_step {V : Type*}
    (G : SimpleGraph V) (x y z : V) (b c : Bool)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hEven : EvenTriple G x y z)
    (hNonadj : ¬ (taylorPairGraph G).Adj (b,x) (c,y)) :
    ∃ d : Bool,
      (taylorPairGraph G).Adj (b,x) (d,z) ∧
        (taylorPairGraph G).Adj (c,y) (d,z) := by
  classical
  let d : Bool := if G.Adj x z then b else !b
  have hb : G.Adj x z ↔ b = d := by
    dsimp [d]
    by_cases hxze : G.Adj x z <;> cases b <;> simp_all
  have hn : ¬ (G.Adj x y ↔ b = c) := by
    intro heq
    exact hNonadj ⟨hxy,heq⟩
  have hc : G.Adj y z ↔ c = d := by
    dsimp [d]
    by_cases hxye : G.Adj x y <;>
      by_cases hxze : G.Adj x z <;>
      by_cases hyze : G.Adj y z <;>
      cases b <;> cases c <;>
      simp_all [EvenTriple]
  exact ⟨d,⟨hxz,hb⟩,⟨hyz,hc⟩⟩

/-- An even base triple supplies a three-edge path between
the two lifts of any one of its points. The last edge is
written in reverse order because the graph is undirected. -/
theorem taylor_mates_three_step {V : Type*}
    (G : SimpleGraph V) (x y z : V) (b : Bool)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hEven : EvenTriple G x y z) :
    ∃ c d : Bool,
      (taylorPairGraph G).Adj (b,x) (c,y) ∧
        (taylorPairGraph G).Adj (c,y) (d,z) ∧
        (taylorPairGraph G).Adj (!b,x) (d,z) := by
  classical
  let c : Bool := if G.Adj x y then b else !b
  let d : Bool := if G.Adj y z then c else !c
  have h1 : G.Adj x y ↔ b = c := by
    dsimp [c]
    by_cases hxyE : G.Adj x y <;> cases b <;> simp_all
  have h2 : G.Adj y z ↔ c = d := by
    dsimp [d]
    by_cases hyzE : G.Adj y z <;> cases c <;> simp_all
  have h3 : G.Adj x z ↔ (!b) = d := by
    dsimp [c,d]
    by_cases hxyE : G.Adj x y <;>
      by_cases hxzE : G.Adj x z <;>
      by_cases hyzE : G.Adj y z <;>
      cases b <;>
      simp_all [EvenTriple]
  exact ⟨c,d,⟨hxy,h1⟩,⟨hyz,h2⟩,⟨hxz,h3⟩⟩


/-- Under the even-triple coverage hypothesis the two lifts of
any base point have a three-edge walk but no shorter walk.
This isolates the entire mate-distance part of fibre rigidity. -/
theorem taylor_mates_three_and_not_shorter {V : Type*}
    [Nontrivial V]
    (G : SimpleGraph V)
    (hCoverage : ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z)
    (b : Bool) (x : V) :
    (∃ p q : Bool × V,
      (taylorPairGraph G).Adj (b,x) p ∧
      (taylorPairGraph G).Adj p q ∧
      (taylorPairGraph G).Adj q (!b,x)) ∧
    ¬ (taylorPairGraph G).Adj (b,x) (!b,x) ∧
    ¬ ∃ p : Bool × V,
      (taylorPairGraph G).Adj (b,x) p ∧
      (taylorPairGraph G).Adj (!b,x) p := by
  classical
  obtain ⟨y, hyx⟩ := exists_ne x
  have hxy : x ≠ y := hyx.symm
  obtain ⟨z,hxz,hyz,hEven⟩ := hCoverage x y hxy
  obtain ⟨c,d,h1,h2,h3⟩ :=
    taylor_mates_three_step G x y z b hxy hxz hyz hEven
  constructor
  · refine ⟨(c,y),(d,z),h1,h2,?_⟩
    exact ((taylorPairGraph G).adj_comm _ _).mpr h3
  constructor
  · exact taylor_mates_not_adj G b x
  · exact taylor_mates_no_common_neighbour G b x

/-- Under the same hypothesis, any two vertices from different
fibres have distance at most two (an edge or a common neighbour). -/
theorem taylor_other_fibres_at_most_two {V : Type*}
    (G : SimpleGraph V)
    (hCoverage : ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z)
    (b c : Bool) (x y : V) (hxy : x ≠ y) :
    (taylorPairGraph G).Adj (b,x) (c,y) ∨
      ∃ w : Bool × V,
        (taylorPairGraph G).Adj (b,x) w ∧
          (taylorPairGraph G).Adj w (c,y) := by
  by_cases hadj : (taylorPairGraph G).Adj (b,x) (c,y)
  · exact Or.inl hadj
  · obtain ⟨z,hxz,hyz,hEven⟩ := hCoverage x y hxy
    obtain ⟨d,h1,h2⟩ :=
      taylor_different_fibres_two_step
        G x y z b c hxy hxz hyz hEven hadj
    exact Or.inr ⟨(d,z),h1,
      ((taylorPairGraph G).adj_comm _ _).mpr h2⟩

end EPPAIII.TwoGraphs
