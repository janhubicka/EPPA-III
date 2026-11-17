import EPPAIII.Primitive.RookModel
import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Polar subconstituent certificates in three hyperbolic pairs

The coordinate interface isolates the published polar representation.
All the actual small witness configurations are constructed over the field.
-/

namespace EPPAIII.Primitive

open SimpleGraph

abbrev PolarSix (F : Type*) := Fin 6 → F

/-- Coordinates are ordered as three hyperbolic generators and their three mates. -/
def splitPolarQuadratic {F : Type*} [Field F] (x : PolarSix F) : F :=
  x 0 * x 3 + x 1 * x 4 + x 2 * x 5

def splitPolarPairing {F : Type*} [Field F] (x y : PolarSix F) : F :=
  x 0 * y 3 + x 1 * y 4 + x 2 * y 5 + y 0 * x 3 + y 1 * x 4 + y 2 * x 5

def symplecticPolarPairing {F : Type*} [Field F] (x y : PolarSix F) : F :=
  x 0 * y 3 + x 1 * y 4 + x 2 * y 5 - (y 0 * x 3 + y 1 * x 4 + y 2 * x 5)

/-- A coordinate chart for projective point adjacency on a six-dimensional
subspace, with representatives for the nonzero admissible vectors. -/
structure PolarSixChart {F V : Type*} [Field F] (G : SimpleGraph V)
    (valid : PolarSix F → Prop) (pairing : PolarSix F → PolarSix F → F) where
  point : {v : PolarSix F // v ≠ 0 ∧ valid v} → V
  same_ray : ∀ {x y}, point x = point y → ∃ a : F, ∀ i, x.val i = a * y.val i
  adjacency : ∀ x y, G.Adj (point x) (point y) ↔
    point x ≠ point y ∧ pairing x.val y.val = 0

private def rootVector {F : Type*} [Field F] : PolarSix F :=
  ![1, 0, 0, 0, 0, 0]

private theorem nonzero_of_normalized {F : Type*} [Field F] {x : PolarSix F}
    {i : Fin 6} (h : x i = 1) : x ≠ 0 := by
  intro e
  exact one_ne_zero (h.symm.trans (congrFun e i))

/-- The root at the first hyperbolic generator. -/
def PolarSixChart.root {F V : Type*} [Field F] {G : SimpleGraph V}
    {valid : PolarSix F → Prop} {pairing : PolarSix F → PolarSix F → F}
    (C : PolarSixChart G valid pairing) (hValid : valid rootVector) : V :=
  C.point ⟨rootVector, nonzero_of_normalized (i := 0) rfl, hValid⟩

private theorem normalized_injective {F V : Type*} [Field F] {G : SimpleGraph V}
    {valid : PolarSix F → Prop} {pairing : PolarSix F → PolarSix F → F}
    (C : PolarSixChart G valid pairing)
    {x y : {v : PolarSix F // v ≠ 0 ∧ valid v}} {i : Fin 6}
    (hx : x.val i = 1) (hy : y.val i = 1) (he : C.point x = C.point y) : x = y := by
  obtain ⟨a, ha⟩ := C.same_ray he
  have h := ha i
  rw [hx, hy, mul_one] at h
  apply Subtype.ext
  funext j
  rw [ha j, ← h, one_mul]

private theorem root_ne_of_coordinate {F V : Type*} [Field F] {G : SimpleGraph V}
    {valid : PolarSix F → Prop} {pairing : PolarSix F → PolarSix F → F}
    (C : PolarSixChart G valid pairing) (hValid : valid rootVector)
    (x : {v : PolarSix F // v ≠ 0 ∧ valid v}) {i : Fin 6}
    (hi : rootVector (F := F) i = 0) (hxi : x.val i = 1) : C.root hValid ≠ C.point x := by
  intro h
  obtain ⟨a, ha⟩ := C.same_ray h.symm
  have hAt := ha i
  change x.val i = a * rootVector i at hAt
  rw [hi, mul_zero, hxi] at hAt
  exact one_ne_zero hAt

private def splitGrid {F : Type*} [Field F] (nearRoot : Bool) (a b : F) : PolarSix F :=
  if nearRoot then ![0, 1, a, 0, -(a * b), b]
  else ![-(a * b), a, 0, 1, b, 0]

private theorem splitGrid_valid {F : Type*} [Field F] (nearRoot : Bool) (a b : F) :
    splitPolarQuadratic (splitGrid nearRoot a b) = 0 := by
  cases nearRoot <;> simp [splitPolarQuadratic, splitGrid, Matrix.cons_val]

private theorem splitGrid_pairing {F : Type*} [Field F] (nearRoot : Bool) (a b c d : F) :
    splitPolarPairing (splitGrid nearRoot a b) (splitGrid nearRoot c d) = -((a-c)*(b-d)) := by
  cases nearRoot <;> simp [splitPolarPairing, splitGrid, Matrix.cons_val] <;> ring

private def splitGridPoint {F : Type*} [Field F] (nearRoot : Bool) (a b : F) :
    {v : PolarSix F // v ≠ 0 ∧ splitPolarQuadratic v = 0} :=
  ⟨splitGrid nearRoot a b, nonzero_of_normalized (i := if nearRoot then 1 else 3)
      (by cases nearRoot <;> rfl), splitGrid_valid nearRoot a b⟩

private def splitGrid_law {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun x => splitPolarQuadratic x = 0) splitPolarPairing)
    (f : Fin 3 ↪ F) (nearRoot : Bool) :
    rookGraph 3 ↪g G where
  toFun x := C.point (splitGridPoint nearRoot (f x.1) (f x.2))
  inj' p q h := by
    have e := normalized_injective C (i := if nearRoot then 1 else 3)
      (x := splitGridPoint nearRoot (f p.1) (f p.2))
      (y := splitGridPoint nearRoot (f q.1) (f q.2))
      (by cases nearRoot <;> rfl) (by cases nearRoot <;> rfl) h
    have he := congrArg Subtype.val e
    cases nearRoot
    · exact Prod.ext (f.injective (congrFun he 1)) (f.injective (congrFun he 4))
    · exact Prod.ext (f.injective (congrFun he 2)) (f.injective (congrFun he 5))
  map_rel_iff' := by
    intro p q
    change G.Adj (C.point (splitGridPoint nearRoot (f p.1) (f p.2)))
      (C.point (splitGridPoint nearRoot (f q.1) (f q.2))) ↔ _
    rw [C.adjacency]
    change (_ ≠ _ ∧ splitPolarPairing (splitGrid nearRoot _ _) (splitGrid nearRoot _ _) = 0)
      ↔ p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)
    rw [splitGrid_pairing, neg_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
      f.injective.eq_iff, f.injective.eq_iff]
    refine and_congr ?_ Iff.rfl
    constructor
    · exact fun hn h => hn (congrArg (fun x : Fin 3 × Fin 3 =>
      C.point (splitGridPoint nearRoot (f x.1) (f x.2))) h)
    · intro hn h
      apply hn
      have e := normalized_injective C (i := if nearRoot then 1 else 3)
        (by cases nearRoot <;> rfl) (by cases nearRoot <;> rfl) h
      have he := congrArg Subtype.val e
      cases nearRoot
      · exact Prod.ext (f.injective (congrFun he 1)) (f.injective (congrFun he 4))
      · exact Prod.ext (f.injective (congrFun he 2)) (f.injective (congrFun he 5))

/-- The first hyperbolic generator is singular for the split quadratic form. -/
theorem splitPolar_root_valid {F : Type*} [Field F] :
    splitPolarQuadratic (rootVector (F := F)) = 0 := by
  simp [splitPolarQuadratic, rootVector, Matrix.cons_val]

/-- In a split chart over a field with at least three scalars, the first
constituent contains the nine-vertex rook graph. -/
def splitPolar_local_rookThree {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun x => splitPolarQuadratic x = 0) splitPolarPairing)
    (f : Fin 3 ↪ F) : rookGraph 3 ↪g localGraph G (C.root splitPolar_root_valid) where
  toFun x := ⟨splitGrid_law C f true x, by
    change G.Adj (C.root splitPolar_root_valid) (C.point (splitGridPoint true (f x.1) (f x.2)))
    rw [PolarSixChart.root, C.adjacency]
    exact ⟨root_ne_of_coordinate C splitPolar_root_valid _ (i := 1) rfl rfl, by
      simp [rootVector, splitPolarPairing, splitGrid, splitGridPoint, Matrix.cons_val]⟩⟩
  inj' := fun p q h => (splitGrid_law C f true).injective (congrArg Subtype.val h)
  map_rel_iff' := (splitGrid_law C f true).map_rel_iff

/-- In the same chart the second constituent contains the nine-vertex
rook graph, using the affine representatives with first mate coordinate one. -/
def splitPolar_nonlocal_rookThree {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun x => splitPolarQuadratic x = 0) splitPolarPairing)
    (f : Fin 3 ↪ F) : rookGraph 3 ↪g nonlocalGraph G (C.root splitPolar_root_valid) where
  toFun x := ⟨splitGrid_law C f false x, by
    change C.root splitPolar_root_valid ≠ C.point (splitGridPoint false (f x.1) (f x.2)) ∧
      ¬ G.Adj (C.root splitPolar_root_valid) (C.point (splitGridPoint false (f x.1) (f x.2)))
    refine ⟨root_ne_of_coordinate C splitPolar_root_valid _ (i := 3) rfl rfl, ?_⟩
    rw [PolarSixChart.root, C.adjacency]
    simp [rootVector, splitPolarPairing, splitGrid, splitGridPoint, Matrix.cons_val]⟩
  inj' := fun p q h => (splitGrid_law C f false).injective (congrArg Subtype.val h)
  map_rel_iff' := (splitGrid_law C f false).map_rel_iff

private def symplecticVector {F : Type*} [Field F] (nearRoot : Bool) (i : Fin 5) : PolarSix F :=
  let r : F := if nearRoot then 1 else 0
  let s : F := if nearRoot then 0 else 1
  ![![r,1,0,s,0,0], ![r,0,1,s,0,0], ![r,0,1,s,1,0],
    ![r,1,0,s,1,1], ![r,0,0,s,0,1]] i

private theorem symplecticVector_injective {F : Type*} [Field F] (nearRoot : Bool) :
    Function.Injective (symplecticVector (F := F) nearRoot) := by
  intro p q h
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  fin_cases p <;> fin_cases q <;>
    simp_all [symplecticVector, Matrix.cons_val]

private theorem symplecticVector_law {F : Type*} [Field F] (nearRoot : Bool)
    (p q : Fin 5) : p ≠ q ∧ symplecticPolarPairing
      (symplecticVector (F := F) nearRoot p) (symplecticVector nearRoot q) = 0
        ↔ (cycleGraph 5).Adj p q := by
  cases nearRoot <;> fin_cases p <;> fin_cases q <;>
    simp [symplecticPolarPairing, symplecticVector, cycleGraph, Matrix.cons_val] <;> decide

private theorem symplecticVector_normal {F : Type*} [Field F] (nearRoot : Bool) (p : Fin 5) :
    symplecticVector (F := F) nearRoot p (if nearRoot then 0 else 3) = 1 := by
  cases nearRoot <;> fin_cases p <;> rfl

private def symplecticPoint {F : Type*} [Field F] (nearRoot : Bool) (p : Fin 5) :
    {v : PolarSix F // v ≠ 0 ∧ True} :=
  ⟨symplecticVector nearRoot p, nonzero_of_normalized (symplecticVector_normal nearRoot p), trivial⟩

private def symplecticPentagonEmbedding {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun _ => True) symplecticPolarPairing)
    (nearRoot : Bool) : cycleGraph 5 ↪g G where
  toFun p := C.point (symplecticPoint nearRoot p)
  inj' p q h := by
    apply symplecticVector_injective (F := F) nearRoot
    exact congrArg Subtype.val
      (normalized_injective C (symplecticVector_normal nearRoot p) (symplecticVector_normal nearRoot q) h)
  map_rel_iff' := by
    intro p q
    change G.Adj (C.point (symplecticPoint nearRoot p)) (C.point (symplecticPoint nearRoot q)) ↔ _
    rw [C.adjacency]
    exact (and_congr (not_congr ⟨fun h => symplecticVector_injective nearRoot
        (congrArg Subtype.val (normalized_injective C (symplecticVector_normal nearRoot p)
          (symplecticVector_normal nearRoot q) h)), fun h => congrArg (fun p => C.point (symplecticPoint nearRoot p)) h⟩) Iff.rfl).trans
      (symplecticVector_law nearRoot p q)

private theorem root_ne_symplecticPoint {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun _ => True) symplecticPolarPairing) (nearRoot : Bool) (p : Fin 5) :
    C.root trivial ≠ C.point (symplecticPoint nearRoot p) := by
  fin_cases p
  · exact root_ne_of_coordinate C trivial _ (i := 1) rfl rfl
  · exact root_ne_of_coordinate C trivial _ (i := 2) rfl rfl
  · exact root_ne_of_coordinate C trivial _ (i := 2) rfl rfl
  · exact root_ne_of_coordinate C trivial _ (i := 1) rfl rfl
  · exact root_ne_of_coordinate C trivial _ (i := 5) rfl rfl

/-- The five explicit alternating-form vectors give a pentagon in the first
constituent of a symplectic chart. -/
def symplecticPolar_local_pentagon {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun _ => True) symplecticPolarPairing) :
    cycleGraph 5 ↪g localGraph G (C.root trivial) where
  toFun p := ⟨symplecticPentagonEmbedding C true p, by
    change G.Adj (C.root trivial) (C.point (symplecticPoint true p))
    rw [PolarSixChart.root, C.adjacency]
    refine ⟨root_ne_symplecticPoint C true p, ?_⟩
    fin_cases p <;> simp [symplecticPoint, symplecticVector, symplecticPolarPairing,
      rootVector, Matrix.cons_val]⟩
  inj' := fun p q h => (symplecticPentagonEmbedding C true).injective (congrArg Subtype.val h)
  map_rel_iff' := (symplecticPentagonEmbedding C true).map_adj_iff

/-- The same vectors shifted by the first mate give a pentagon in the
second constituent of a symplectic chart. -/
def symplecticPolar_nonlocal_pentagon {F V : Type*} [Field F] {G : SimpleGraph V}
    (C : PolarSixChart (F := F) G (fun _ => True) symplecticPolarPairing) :
    cycleGraph 5 ↪g nonlocalGraph G (C.root trivial) where
  toFun p := ⟨symplecticPentagonEmbedding C false p, by
    change C.root trivial ≠ C.point (symplecticPoint false p) ∧
      ¬ G.Adj (C.root trivial) (C.point (symplecticPoint false p))
    refine ⟨root_ne_symplecticPoint C false p, ?_⟩
    rw [PolarSixChart.root, C.adjacency]
    fin_cases p <;> simp [symplecticPoint, symplecticVector, symplecticPolarPairing,
      rootVector, Matrix.cons_val]⟩
  inj' := fun p q h => (symplecticPentagonEmbedding C false).injective (congrArg Subtype.val h)
  map_rel_iff' := (symplecticPentagonEmbedding C false).map_adj_iff

end EPPAIII.Primitive
