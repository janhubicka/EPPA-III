import EPPAIII.CliqueCovers.WagnerSquareOrbits
import EPPAIII.EPPA.Definitions

/-!
# The dihedral action on the four Wagner profile corners

The four outside neighbourhood profiles in the two-partial
s=t=2 case are indexed by pairs of bits. Independent swaps of the
chosen base K₂ vertices flip the two bits; exchanging the two base
cliques transposes them.

The eight generated permutations act transitively on ordered side
pairs (one bit changes) and separately on ordered opposite pairs
(both bits change). Hence an invariant outside graph has two
Boolean adjacency parameters. Together with the two-edge count
this yields the opposite-corner matching.

The further identification of this action with actual EPPA lifts,
and the eight-vertex Wagner host, remains a separate obligation.
-/

namespace EPPAIII.CliqueCovers

/-- Flip the first bit of a square corner. -/
def squareFlipFirst : Equiv.Perm (Bool × Bool) where
  toFun := fun x => (!x.1, x.2)
  invFun := fun x => (!x.1, x.2)
  left_inv := by rintro ⟨a,b⟩; cases a <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases a <;> rfl

/-- Flip the second bit. -/
def squareFlipSecond : Equiv.Perm (Bool × Bool) where
  toFun := fun x => (x.1, !x.2)
  invFun := fun x => (x.1, !x.2)
  left_inv := by rintro ⟨a,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases b <;> rfl

/-- Exchange the two base clique coordinates. -/
def squareSwapCoordinates : Equiv.Perm (Bool × Bool) where
  toFun := fun x => (x.2, x.1)
  invFun := fun x => (x.2, x.1)
  left_inv := by rintro ⟨a,b⟩; rfl
  right_inv := by rintro ⟨a,b⟩; rfl

/-- All eight coordinate-symmetry permutations of the square. -/
def squareAction (flipA flipB swap : Bool) :
    Equiv.Perm (Bool × Bool) :=
  (if swap then squareSwapCoordinates else Equiv.refl _).trans
    ((if flipA then squareFlipFirst else Equiv.refl _).trans
      (if flipB then squareFlipSecond else Equiv.refl _))

/-- A side pair differs in exactly one coordinate. -/
def squareSideStatus (x y : Bool × Bool) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.1 ≠ y.1 ∧ x.2 = y.2)

/-- An opposite pair differs in both coordinates. -/
def squareOppositeStatus (x y : Bool × Bool) : Prop :=
  x.1 ≠ y.1 ∧ x.2 ≠ y.2

/-- The eight generated symmetries reach every ordered side pair. -/
theorem squareAction_side_transitive (x y : Bool × Bool)
    (hSide : squareSideStatus x y) :
    ∃ a b c : Bool,
      squareAction a b c (false,false) = x ∧
      squareAction a b c (false,true) = y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp_all [squareSideStatus, squareAction,
      squareFlipFirst, squareFlipSecond, squareSwapCoordinates] <;>
    decide

/-- The same symmetries reach every ordered opposite pair. -/
theorem squareAction_opposite_transitive (x y : Bool × Bool)
    (hOpposite : squareOppositeStatus x y) :
    ∃ a b c : Bool,
      squareAction a b c (false,false) = x ∧
      squareAction a b c (true,true) = y := by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
    simp_all [squareOppositeStatus, squareAction,
      squareFlipFirst, squareFlipSecond, squareSwapCoordinates] <;>
    decide

/-- An automorphism followed by another remains an automorphism. -/
private theorem graphAutomorphism_trans {V : Type*}
    (B : SimpleGraph V) (p q : Equiv.Perm V)
    (hp : IsGraphAutomorphism B p)
    (hq : IsGraphAutomorphism B q) :
    IsGraphAutomorphism B (p.trans q) := by
  intro x y
  exact (hp x y).trans (hq (p x) (p y))

/-- Invariance under the three generators entails invariance
under all eight generated square symmetries. -/
theorem squareAction_graphAut
    (B : SimpleGraph (Bool × Bool))
    (hA : IsGraphAutomorphism B squareFlipFirst)
    (hB : IsGraphAutomorphism B squareFlipSecond)
    (hSwap : IsGraphAutomorphism B squareSwapCoordinates)
    (a b c : Bool) :
    IsGraphAutomorphism B (squareAction a b c) := by
  have hId : IsGraphAutomorphism B (Equiv.refl _) := by
    intro x y
    rfl
  have ha :
      IsGraphAutomorphism B
        (if a then squareFlipFirst else Equiv.refl _) := by
    cases a
    · simpa using hId
    · simpa using hA
  have hb :
      IsGraphAutomorphism B
        (if b then squareFlipSecond else Equiv.refl _) := by
    cases b
    · simpa using hId
    · simpa using hB
  have hc :
      IsGraphAutomorphism B
        (if c then squareSwapCoordinates else Equiv.refl _) := by
    cases c
    · simpa using hId
    · simpa using hSwap
  exact graphAutomorphism_trans B _ _ hc
    (graphAutomorphism_trans B _ _ ha hb)

/-- Every graph invariant under the three corner generators is
one of the four two-parameter square corner graphs. -/
theorem square_invariant_graph_two_parameters
    (B : SimpleGraph (Bool × Bool))
    (hA : IsGraphAutomorphism B squareFlipFirst)
    (hB : IsGraphAutomorphism B squareFlipSecond)
    (hSwap : IsGraphAutomorphism B squareSwapCoordinates) :
    ∃ side opposite : Bool, B = squareCornerGraph side opposite := by
  classical
  let side : Bool := decide (B.Adj (false,false) (false,true))
  let opposite : Bool := decide (B.Adj (false,false) (true,true))
  have hSideValue :
      B.Adj (false,false) (false,true) ↔ side = true := by
    simp [side]
  have hOppValue :
      B.Adj (false,false) (true,true) ↔ opposite = true := by
    simp [opposite]
  have hSide (x y : Bool × Bool)
      (h : squareSideStatus x y) :
      B.Adj x y ↔ side = true := by
    obtain ⟨a,b,c,hx,hy⟩ := squareAction_side_transitive x y h
    have hAut := squareAction_graphAut B hA hB hSwap a b c
    have hTransport :
        B.Adj (false,false) (false,true) ↔ B.Adj x y := by
      simpa [hx,hy] using hAut (false,false) (false,true)
    exact hTransport.symm.trans hSideValue
  have hOpp (x y : Bool × Bool)
      (h : squareOppositeStatus x y) :
      B.Adj x y ↔ opposite = true := by
    obtain ⟨a,b,c,hx,hy⟩ := squareAction_opposite_transitive x y h
    have hAut := squareAction_graphAut B hA hB hSwap a b c
    have hTransport :
        B.Adj (false,false) (true,true) ↔ B.Adj x y := by
      simpa [hx,hy] using hAut (false,false) (true,true)
    exact hTransport.symm.trans hOppValue
  refine ⟨side,opposite,?_⟩
  apply SimpleGraph.ext
  funext x y
  apply propext
  change B.Adj x y ↔ squareCornerAdj side opposite x y
  by_cases hxy : x = y
  · subst y
    simp [squareCornerAdj]
  by_cases hOpposite : squareOppositeStatus x y
  · have h := hOpp x y hOpposite
    simpa [squareCornerAdj, squareOppositeStatus,
      hOpposite] using h
  · have hIsSide : squareSideStatus x y := by
      rcases x with ⟨x₁,x₂⟩
      rcases y with ⟨y₁,y₂⟩
      cases x₁ <;> cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp_all [squareSideStatus, squareOppositeStatus]
    have h := hSide x y hIsSide
    simpa [squareCornerAdj, squareSideStatus,
      squareOppositeStatus, hOpposite, hIsSide] using h

/-- If the square action preserves a graph with two edges, the graph
is exactly the opposite-corner matching. -/
theorem square_invariant_two_edges_is_opposite_matching
    (B : SimpleGraph (Bool × Bool))
    [DecidableRel B.Adj]
    (hA : IsGraphAutomorphism B squareFlipFirst)
    (hB : IsGraphAutomorphism B squareFlipSecond)
    (hSwap : IsGraphAutomorphism B squareSwapCoordinates)
    (hEdges : B.edgeFinset.card = 2) :
    B = squareCornerGraph false true := by
  classical
  obtain ⟨side,opposite,hEq⟩ :=
    square_invariant_graph_two_parameters B hA hB hSwap
  have hIntrinsic : B.edgeSet.ncard = 2 := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hEdges
  rw [hEq] at hIntrinsic
  have hPattern :
      (squareCornerGraph side opposite).edgeFinset.card = 2 := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hIntrinsic
  obtain ⟨hs,ho⟩ :=
    squareCornerGraph_two_edges side opposite hPattern
  simpa [hs,ho] using hEq

end EPPAIII.CliqueCovers
