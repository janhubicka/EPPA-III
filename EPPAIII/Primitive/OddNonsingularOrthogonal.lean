import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fin.VecNotation

/-! # Odd-dimensional nonsingular orthogonal constituent certificates -/

namespace EPPAIII.Primitive

/-- The fields in the odd nonsingular point and hyperplane rows. -/
inductive OddOrthogonalField
  | three | four | eight

namespace OddOrthogonalField

/-- The field order for coordinate digits. -/
def order : OddOrthogonalField → ℕ
  | three => 3
  | four => 4
  | eight => 8

/-- The seed dimension. Each additional hyperbolic pair adds two coordinates. -/
def seedWidth : OddOrthogonalField → ℕ
  | three => 7
  | four | eight => 4

private def add (f : OddOrthogonalField) (a b : ℕ) : ℕ :=
  match f with
  | three => (a + b) % 3
  | four | eight => Nat.xor a b

private def binaryDouble (q polynomial a : ℕ) : ℕ :=
  if 2 * a < q then 2 * a else Nat.xor (2 * a) polynomial

private def binaryMultiply (q poly a b : ℕ) : ℕ :=
  let da := binaryDouble q poly a
  let dda := binaryDouble q poly da
  Nat.xor (if b.testBit 0 then a else 0)
    (Nat.xor (if b.testBit 1 then da else 0) (if b.testBit 2 then dda else 0))

private def mul (f : OddOrthogonalField) (a b : ℕ) : ℕ :=
  match f with
  | three => a * b % 3
  | four => binaryMultiply 4 7 a b
  | eight => binaryMultiply 8 11 a b

private def square (f : OddOrthogonalField) (a : ℕ) : ℕ := f.mul a a

private def coord (f : OddOrthogonalField) (v : Fin f.seedWidth → ℕ) (i : ℕ) : ℕ :=
  if h : i < f.seedWidth then v ⟨i, h⟩ else 0

private def Q (f : OddOrthogonalField) (plus : Bool) (v : Fin f.seedWidth → ℕ) : ℕ :=
  let x := f.coord v
  match f with
  | three => (x 0 * x 0 + x 1 * x 2 + x 3 * x 4 + x 5 * x 6) % 3
  | four | eight =>
    let hyperbolic := f.add (f.mul (x 0) (x 1)) (f.mul (x 2) (x 3))
    if plus then hyperbolic else
      f.add hyperbolic (f.add (f.square (x 0)) (f.mul (if f.order = 4 then 2 else 1) (f.square (x 1))))

private def B (f : OddOrthogonalField) (v w : Fin f.seedWidth → ℕ) : ℕ :=
  let x := f.coord v
  let y := f.coord w
  let pair i := f.add (f.mul (x i) (y (i + 1))) (f.mul (x (i + 1)) (y i))
  match f with
  | three => f.add (2 * x 0 * y 0 % 3) (f.add (pair 1) (f.add (pair 3) (pair 5)))
  | four | eight => f.add (pair 0) (pair 2)

private def trace (f : OddOrthogonalField) (a : ℕ) : ℕ :=
  let a2 := f.square a
  let a4 := f.square a2
  match f with
  | three => a
  | four => f.add a a2
  | eight => f.add (f.add a a2) a4

/-- Coordinate representation of the seed part and the additional hyperbolic pairs. -/
def Coordinates (f : OddOrthogonalField) (d : ℕ) :=
  (Fin f.seedWidth → Fin f.order) × (Fin d → Fin f.order × Fin f.order)

instance (f : OddOrthogonalField) (d : ℕ) : DecidableEq (f.Coordinates d) := by
  unfold Coordinates
  infer_instance

private def form (f : OddOrthogonalField) (plus : Bool) {d : ℕ} (v : f.Coordinates d) : ℕ :=
  f.add (f.Q plus (fun i => (v.1 i).val))
    ((List.ofFn fun i => f.mul (v.2 i).1.val (v.2 i).2.val).foldl f.add 0)

private def polar (f : OddOrthogonalField) {d : ℕ} (v w : f.Coordinates d) : ℕ :=
  f.add (f.B (fun i => (v.1 i).val) (fun i => (w.1 i).val))
    ((List.ofFn fun i => f.add (f.mul (v.2 i).1.val (w.2 i).2.val)
      (f.mul (v.2 i).2.val (w.2 i).1.val)).foldl f.add 0)

private def formSum (f : OddOrthogonalField) (plus : Bool) {d : ℕ} (v w : f.Coordinates d) : ℕ :=
  f.add (f.Q plus (fun i => f.add (v.1 i).val (w.1 i).val))
    ((List.ofFn fun i => f.mul (f.add (v.2 i).1.val (w.2 i).1.val)
      (f.add (v.2 i).2.val (w.2 i).2.val)).foldl f.add 0)

private def representative (f : OddOrthogonalField) {d : ℕ} (v : f.Coordinates d) : Bool :=
  let digits := (List.ofFn fun i => (v.1 i).val) ++
      ((List.ofFn fun i => [(v.2 i).1.val, (v.2 i).2.val]).flatten)
  (digits.find? (· != 0)) == some 1

private def isTernary : OddOrthogonalField → Bool
  | three => true
  | four | eight => false

private def valid (f : OddOrthogonalField) (plus : Bool) {d : ℕ} (v : f.Coordinates d) : Bool :=
  let q := f.form plus v
  if f.isTernary then f.representative v && q == (if plus then 1 else 2) else f.trace q == 0

private def adjacent (f : OddOrthogonalField) (plus : Bool) {d : ℕ} (v w : f.Coordinates d) : Bool :=
  let b := f.polar v w
  if f.isTernary then b == 0 else f.add (f.formSum plus v w) (f.square b) != 0

/-- Projective norm points for q=3 and trace-zero form coordinates for q=4,8. -/
def Point (f : OddOrthogonalField) (plus : Bool) (d : ℕ) :=
  {v : f.Coordinates d // f.valid plus v = true}

instance (f : OddOrthogonalField) (plus : Bool) (d : ℕ) : DecidableEq (f.Point plus d) := by
  unfold Point
  infer_instance

/-- The orthogonality orientation in odd characteristic and the complementary
tangent orientation of the quadratic-form graph in even characteristic. -/
def graph (f : OddOrthogonalField) (plus : Bool) (d : ℕ) : SimpleGraph (f.Point plus d) where
  Adj v w := v ≠ w ∧ f.adjacent plus v.val w.val = true ∧ f.adjacent plus w.val v.val = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (f : OddOrthogonalField) (plus : Bool) (d : ℕ) :
    DecidableRel (f.graph plus d).Adj := fun _ _ => by
  change Decidable (_ ∧ _ ∧ _)
  infer_instance

private def digits (f : OddOrthogonalField) (n : ℕ) : Fin f.seedWidth → Fin f.order :=
  fun i => ⟨n / 10 ^ (f.seedWidth - 1 - i.val) % 10 % f.order,
    Nat.mod_lt _ (by cases f <;> decide)⟩

private def seedData (f : OddOrthogonalField) (plus : Bool) : Fin 11 → ℕ :=
  match f, plus with
  | three, true =>
    ![1000000, 0000011, 0120221, 0001102, 0122211, 0012200,
      1000001, 1110112, 1110221, 1200201, 1100010]
  | three, false =>
    ![0000012, 0001200, 1102200, 1202011, 1000111, 0120000,
      0000112, 1102220, 1001212, 1012121, 0101021]
  | four, true => ![0, 0011, 3230, 2032, 3200, 1231, 0001, 0220, 3002, 1212, 0120]
  | four, false => ![0, 0200, 1231, 0122, 0220, 1003, 0001, 0223, 1212, 2113, 0232]
  | eight, true => ![0, 0012, 0075, 0157, 0037, 0014, 0001, 0220, 7000, 0205, 0030]
  | eight, false => ![0, 0200, 0401, 0220, 0053, 0402, 0001, 0562, 0010, 0416, 0050]

private def zeroDigit (f : OddOrthogonalField) : Fin f.order :=
  ⟨0, by cases f <;> decide⟩

private def seedCoordinates (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i : Fin 11) :
    f.Coordinates d :=
  (f.digits (f.seedData plus i), fun _ => (f.zeroDigit, f.zeroDigit))

private theorem fold_zeros (f : OddOrthogonalField) (n a : ℕ) (h : f.add a 0 = a) :
    (List.replicate n 0).foldl f.add a = a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.foldl_cons, h, ih]

private theorem form_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i : Fin 11) :
    f.form plus (f.seedCoordinates plus d i) = f.form plus (f.seedCoordinates plus 0 i) := by
  unfold form seedCoordinates zeroDigit
  have hMul : f.mul 0 0 = 0 := by cases f <;> decide
  simp only [hMul, List.ofFn_const]
  rw [fold_zeros f d 0 (by cases f <;> decide)]
  rfl

private theorem polar_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i j : Fin 11) :
    f.polar (f.seedCoordinates plus d i) (f.seedCoordinates plus d j) =
      f.polar (f.seedCoordinates plus 0 i) (f.seedCoordinates plus 0 j) := by
  unfold polar seedCoordinates zeroDigit
  have hZero : f.add (f.mul 0 0) (f.mul 0 0) = 0 := by cases f <;> decide
  simp only [hZero, List.ofFn_const]
  rw [fold_zeros f d 0 (by cases f <;> decide)]
  rfl

private theorem formSum_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i j : Fin 11) :
    f.formSum plus (f.seedCoordinates plus d i) (f.seedCoordinates plus d j) =
      f.formSum plus (f.seedCoordinates plus 0 i) (f.seedCoordinates plus 0 j) := by
  unfold formSum seedCoordinates zeroDigit
  have hZero : f.mul (f.add 0 0) (f.add 0 0) = 0 := by cases f <;> decide
  simp only [hZero, List.ofFn_const]
  rw [fold_zeros f d 0 (by cases f <;> decide)]
  rfl

private theorem find_append_zero (l r : List ℕ) (h : ∀ x ∈ r, x = 0) :
    (l ++ r).find? (· != 0) = l.find? (· != 0) := by
  rw [List.find?_append]
  have hempty : r.find? (· != 0) = none := by
    apply List.find?_eq_none.mpr
    intro x hx
    rw [h x hx]
    decide
  simp only [hempty, Option.or_none]

private theorem representative_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i : Fin 11) :
    f.representative (f.seedCoordinates plus d i) =
      f.representative (f.seedCoordinates plus 0 i) := by
  unfold representative seedCoordinates zeroDigit
  dsimp only
  rw [find_append_zero, find_append_zero]
  all_goals simp

private theorem valid_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i : Fin 11) :
    f.valid plus (f.seedCoordinates plus d i) = true := by
  unfold valid
  dsimp only
  rw [form_seed, representative_seed]
  revert i
  cases f <;> cases plus <;> decide

private theorem adjacent_seed (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i j : Fin 11) :
    f.adjacent plus (f.seedCoordinates plus d i) (f.seedCoordinates plus d j) =
      f.adjacent plus (f.seedCoordinates plus 0 i) (f.seedCoordinates plus 0 j) := by
  unfold adjacent
  dsimp only
  rw [polar_seed, formSum_seed]

private def seedPoint (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i : Fin 11) :
    f.Point plus d := ⟨f.seedCoordinates plus d i, valid_seed f plus d i⟩

private theorem seedPoint_injective (f : OddOrthogonalField) (plus : Bool) (d : ℕ) :
    Function.Injective (f.seedPoint plus d) := by
  have hd : Function.Injective (fun i => f.digits (f.seedData plus i)) := by
    cases f <;> cases plus <;> decide
  intro i j h
  exact hd (congrArg (fun v : f.Point plus d => v.val.1) h)

private theorem seedPoint_adj (f : OddOrthogonalField) (plus : Bool) (d : ℕ) (i j : Fin 11) :
    (f.graph plus d).Adj (f.seedPoint plus d i) (f.seedPoint plus d j) ↔
      (f.graph plus 0).Adj (f.seedPoint plus 0 i) (f.seedPoint plus 0 j) := by
  change (_ ≠ _ ∧ f.adjacent plus (f.seedCoordinates plus d i) (f.seedCoordinates plus d j) = true ∧
    f.adjacent plus (f.seedCoordinates plus d j) (f.seedCoordinates plus d i) = true) ↔
      (_ ≠ _ ∧ f.adjacent plus (f.seedCoordinates plus 0 i) (f.seedCoordinates plus 0 j) = true ∧
      f.adjacent plus (f.seedCoordinates plus 0 j) (f.seedCoordinates plus 0 i) = true)
  rw [(seedPoint_injective f plus d).ne_iff, (seedPoint_injective f plus 0).ne_iff,
    adjacent_seed f plus d i j, adjacent_seed f plus d j i]

private def neighborIndex (i : Fin 5) : Fin 11 :=
  ⟨i.val + 1, by omega⟩

private def nonneighborIndex (i : Fin 5) : Fin 11 :=
  ⟨i.val + 6, by omega⟩

private theorem neighborIndex_injective : Function.Injective neighborIndex := by decide
private theorem nonneighborIndex_injective : Function.Injective nonneighborIndex := by decide

private theorem local_members (f : OddOrthogonalField) (plus : Bool) :
    ∀ i, (f.graph plus 0).Adj (f.seedPoint plus 0 0) (f.seedPoint plus 0 (neighborIndex i)) := by
  cases f <;> cases plus <;> decide

private theorem nonlocal_members (f : OddOrthogonalField) (plus : Bool) :
    ∀ i, ¬ (f.graph plus 0).Adj (f.seedPoint plus 0 0) (f.seedPoint plus 0 (nonneighborIndex i)) := by
  cases f <;> cases plus <;> decide

private theorem local_edges (f : OddOrthogonalField) (plus : Bool) :
    ∀ i j, (f.graph plus 0).Adj (f.seedPoint plus 0 (neighborIndex i))
      (f.seedPoint plus 0 (neighborIndex j)) ↔ (SimpleGraph.cycleGraph 5).Adj i j := by
  cases f <;> cases plus <;> decide

private theorem nonlocal_edges (f : OddOrthogonalField) (plus : Bool) :
    ∀ i j, (f.graph plus 0).Adj (f.seedPoint plus 0 (nonneighborIndex i))
      (f.seedPoint plus 0 (nonneighborIndex j)) ↔ (SimpleGraph.cycleGraph 5).Adj i j := by
  cases f <;> cases plus <;> decide

/-- Both constituents at the coordinate root have induced pentagons. -/
theorem coordinatePentagons (f : OddOrthogonalField) (plus : Bool) (d : ℕ) :
    Nonempty (SimpleGraph.cycleGraph 5 ↪g localGraph (f.graph plus d) (f.seedPoint plus d 0)) ∧
    Nonempty (SimpleGraph.cycleGraph 5 ↪g nonlocalGraph (f.graph plus d) (f.seedPoint plus d 0)) := by
  constructor
  · exact ⟨⟨⟨fun i => ⟨f.seedPoint plus d (neighborIndex i),
        (seedPoint_adj f plus d _ _).mpr (local_members f plus i)⟩,
      fun _ _ h => neighborIndex_injective (seedPoint_injective f plus d (congrArg Subtype.val h))⟩,
      fun {i j} => (seedPoint_adj f plus d _ _).trans (local_edges f plus i j)⟩⟩
  · exact ⟨⟨⟨fun i => ⟨f.seedPoint plus d (nonneighborIndex i),
        (seedPoint_injective f plus d).ne (by intro h; have := congrArg Fin.val h; simp [nonneighborIndex] at this),
        fun h => nonlocal_members f plus i ((seedPoint_adj f plus d _ _).mp h)⟩,
      fun _ _ h => nonneighborIndex_injective (seedPoint_injective f plus d (congrArg Subtype.val h))⟩,
      fun {i j} => (seedPoint_adj f plus d _ _).trans (nonlocal_edges f plus i j)⟩⟩

/-- Transport the rooted certificates throughout a transitive coordinate model. -/
theorem constituentPentagons (f : OddOrthogonalField) (plus : Bool) (d : ℕ)
    (hTrans : ∀ r s, ∃ a : f.graph plus d ≃g f.graph plus d, a r = s)
    (root : f.Point plus d) :
    Nonempty (SimpleGraph.cycleGraph 5 ↪g localGraph (f.graph plus d) root) ∧
    Nonempty (SimpleGraph.cycleGraph 5 ↪g nonlocalGraph (f.graph plus d) root) := by
  obtain ⟨⟨a⟩, ⟨b⟩⟩ := coordinatePentagons f plus d
  obtain ⟨φ, hφ⟩ := hTrans (f.seedPoint plus d 0) root
  rw [← hφ]
  exact ⟨⟨(localIso φ _).toEmbedding.comp a⟩, ⟨(nonlocalIso φ _).toEmbedding.comp b⟩⟩

end OddOrthogonalField
end EPPAIII.Primitive
