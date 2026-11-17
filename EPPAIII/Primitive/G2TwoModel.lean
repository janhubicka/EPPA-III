import EPPAIII.Primitive.FanoConstituents
import EPPAIII.Primitive.Subconstituents

/-! # The Fano construction of the order-36 G₂(2) graph

The vertex labels and incidences follow the 1 + 14 + 21 construction in
Brouwer and Van Maldeghem, Section 10.14. The named graph identification
uses that construction. The graph parameters and rooted models are proved.
-/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The distinguished vertex `none`, then the points, lines and flags. -/
abbrev G2TwoVertex := Option (Sum (Sum (Fin 7) (Fin 7)) FanoFlag)

private def g2TwoAdj : G2TwoVertex → G2TwoVertex → Prop
  | none, some (.inl _) => True
  | some (.inl _), none => True
  | some (.inl x), some (.inl y) => fanoNonincidenceGraph.Adj x y
  | some (.inr x), some (.inr y) => fanoFlagGraph.Adj x y
  | some (.inl (.inl p)), some (.inr f) => p ∈ fanoLines f.val.2
  | some (.inr f), some (.inl (.inl p)) => p ∈ fanoLines f.val.2
  | some (.inl (.inr L)), some (.inr f) => f.val.1 ∈ fanoLines L
  | some (.inr f), some (.inl (.inr L)) => f.val.1 ∈ fanoLines L
  | _, _ => False

/-- The order-36 graph obtained from the Fano point-line and flag models. -/
def g2TwoGraph : SimpleGraph G2TwoVertex where
  Adj := g2TwoAdj
  symm := ⟨by
    rintro (_ | (_ | _)) (_ | (_ | _)) h
    all_goals try first
      | exact h
      | exact fanoNonincidenceGraph.adj_symm h
      | exact fanoFlagGraph.adj_symm h
    all_goals rename_i x y
    all_goals first | (cases x <;> exact h) | (cases y <;> exact h)⟩
  loopless := ⟨by
    rintro (_ | (_ | _)) h <;>
      first | exact h | exact fanoNonincidenceGraph.irrefl h | exact fanoFlagGraph.irrefl h⟩

instance : DecidableRel g2TwoGraph.Adj := by
  intro a b
  change Decidable (g2TwoAdj a b)
  rcases a with (_ | ((_ | _) | _)) <;> rcases b with (_ | ((_ | _) | _)) <;>
    simp only [g2TwoAdj] <;> infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Strong regularity of the concrete construction, checked on the vertex labels. -/
theorem g2Two_isSRG : g2TwoGraph.IsSRGWith 36 14 4 6 := by
  constructor
  · decide
  · change ∀ v, g2TwoGraph.degree v = 14
    decide
  · decide
  · change ∀ a b, a ≠ b → ¬ g2TwoGraph.Adj a b →
       Fintype.card (g2TwoGraph.commonNeighbors a b) = 6
    decide

/-- The first constituent at the distinguished vertex is Fano nonincidence. -/
def g2Two_localIso : fanoNonincidenceGraph ≃g localGraph g2TwoGraph none where
  toEquiv := {
    toFun := fun x => ⟨some (.inl x), trivial⟩
    invFun := fun
      | ⟨some (.inl x), _⟩ => x
      | ⟨none, h⟩ => False.elim h
      | ⟨some (.inr _), h⟩ => False.elim h
    left_inv _ := rfl
    right_inv := by
      rintro ⟨(_ | (_ | _)), h⟩
      · exact False.elim h
      · rfl
      · exact False.elim h }
  map_rel_iff' := Iff.rfl

/-- The other constituent at the distinguished vertex is the Fano flag model. -/
def g2Two_nonlocalIso : fanoFlagGraph ≃g nonlocalGraph g2TwoGraph none where
  toEquiv := {
    toFun := fun x => ⟨some (.inr x), ⟨by simp, id⟩⟩
    invFun := fun
      | ⟨some (.inr x), _⟩ => x
      | ⟨none, h⟩ => False.elim (h.1 rfl)
      | ⟨some (.inl _), h⟩ => False.elim (h.2 trivial)
    left_inv _ := rfl
    right_inv := by
      rintro ⟨(_ | (_ | _)), h⟩
      · exact False.elim (h.1 rfl)
      · exact False.elim (h.2 trivial)
      · rfl }
  map_rel_iff' := Iff.rfl

end EPPAIII.Primitive
