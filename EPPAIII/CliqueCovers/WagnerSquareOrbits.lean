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

/-- The four sides contribute four edges and the opposite matching
contributes two edges, independently of their Boolean statuses. -/
theorem squareCornerGraph_edge_count (side opposite : Bool) :
    (squareCornerGraph side opposite).edgeFinset.card =
      (if side then 4 else 0) + (if opposite then 2 else 0) := by
  cases side <;> cases opposite <;> native_decide

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
  native_decide

end EPPAIII.CliqueCovers
