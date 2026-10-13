import EPPAIII.CliqueCovers.Basic

/-!
# Four-corner graphs in the exceptional s=t=2 orbit

For an outside vertex with one neighbour in each of the two base K₂
components, the four profiles form a square. Its unordered pairs are
the four sides (one coordinate changes) and the two opposite corners
(both coordinates change).

The current module supplies a concrete finite graph model with two
Boolean parameters and its exact edge count. Its later application to
arbitrary EPPA hosts additionally requires showing that the actual
outside adjacency is constant on these two profile-pair orbits.
-/

namespace EPPAIII.CliqueCovers

/-- Which unordered corner-pairs are sides or opposite corners. -/
def squareCornerAdj (side opposite : Bool)
    (x y : Bool × Bool) : Prop :=
  (x.1 ≠ y.1 ∧ x.2 ≠ y.2 ∧ opposite = true) ∨
  (((x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.1 ≠ y.1 ∧ x.2 = y.2)) ∧ side = true)

/-- The two-parameter simple graph on four corners. -/
def squareCornerGraph (side opposite : Bool) :
    SimpleGraph (Bool × Bool) where
  Adj := squareCornerAdj side opposite
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hFirst,hSecond,hOpp⟩ | ⟨hSide,hPresent⟩
    · exact Or.inl ⟨hFirst.symm,hSecond.symm,hOpp⟩
    · apply Or.inr
      constructor
      · rcases hSide with ⟨hEqual,hDiff⟩ | ⟨hDiff,hEqual⟩
        · exact Or.inl ⟨hEqual.symm,hDiff.symm⟩
        · exact Or.inr ⟨hDiff.symm,hEqual.symm⟩
      · exact hPresent
  loopless := by
    constructor
    intro x h
    rcases h with ⟨hDiff,_,_⟩ | ⟨hSide,_⟩
    · exact hDiff rfl
    · rcases hSide with ⟨_,hDiff⟩ | ⟨hDiff,_⟩
      · exact hDiff rfl
      · exact hDiff rfl

/-- Computable adjacency for the finite square patterns, so their
edge counts can be checked without a noncomputable decidability choice. -/
instance squareCornerGraph_decidableAdj (side opposite : Bool) :
    DecidableRel (squareCornerGraph side opposite).Adj := by
  intro x y
  change Decidable (squareCornerAdj side opposite x y)
  unfold squareCornerAdj
  infer_instance

/-- Every corner has two possible side-neighbours and one
opposite corner, so its degree is controlled by the two bits. -/
theorem squareCornerGraph_degree (side opposite : Bool) (v : Bool × Bool) :
    (squareCornerGraph side opposite).degree v =
      (if side then 2 else 0) + (if opposite then 1 else 0) := by
  rcases v with ⟨a,b⟩
  cases a <;> cases b <;> cases side <;> cases opposite <;> decide

/-- The four sides contribute four edges and the opposite matching
contributes two. Use degree-sum rather than evaluating Sym2 edgeFinsets
directly, because the quotient edge-set instance is noncomputable. -/
theorem squareCornerGraph_edge_count (side opposite : Bool) :
    (squareCornerGraph side opposite).edgeFinset.card =
      (if side then 4 else 0) + (if opposite then 2 else 0) := by
  classical
  let d : ℕ := (if side then 2 else 0) + (if opposite then 1 else 0)
  have hReg : (squareCornerGraph side opposite).IsRegularOfDegree d := by
    intro v
    exact squareCornerGraph_degree side opposite v
  have hSum :
      (∑ v : Bool × Bool, (squareCornerGraph side opposite).degree v) =
        4 * d := by
    calc
      _ = ∑ _v : Bool × Bool, d := by
        apply Finset.sum_congr rfl
        intro v _
        exact hReg v
      _ = 4 * d := by simp [Fintype.card_prod, d]
  have hDouble := (squareCornerGraph side opposite).sum_degrees_eq_twice_card_edges
  have hArith :
      2 * d =
        (if side then 4 else 0) + (if opposite then 2 else 0) := by
    cases side <;> cases opposite <;> norm_num [d]
  omega

/-- Exactly two edges force all sides absent and both opposite-corner
edges present. This is the numerical kernel of the Wagner exception. -/
theorem squareCornerGraph_two_edges (side opposite : Bool)
    (h : (squareCornerGraph side opposite).edgeFinset.card = 2) :
    side = false ∧ opposite = true := by
  have hc := squareCornerGraph_edge_count side opposite
  cases side <;> cases opposite <;> simp_all

/-- Opposite corners form a matching of precisely two edges. -/
theorem squareOppositeMatching_edge_count :
    (squareCornerGraph false true).edgeFinset.card = 2 := by
  simpa using (squareCornerGraph_edge_count false true)

end EPPAIII.CliqueCovers
