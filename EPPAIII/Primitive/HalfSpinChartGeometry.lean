import EPPAIII.Primitive.HalfSpinPentagons
import Mathlib.LinearAlgebra.Prod

/-! # The half-spin pentagons in the hyperbolic geometry model -/

namespace EPPAIII.Primitive

open Matrix

private abbrev FiveSpace (F : Type*) := Fin 5 → F

private def graphInfKer {F : Type*} [Field F]
    (A B : Matrix (Fin 5) (Fin 5) F) :
    LinearMap.ker (A - B).mulVecLin ≃ₗ[F] ↥(A.mulVecLin.graph ⊓ B.mulVecLin.graph) where
  toFun x := ⟨(x.val, A.mulVecLin x.val), by
    have hx := LinearMap.mem_ker.mp x.property
    change (A - B).mulVec x.val = 0 at hx
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    exact ⟨rfl, hx⟩⟩
  invFun p := ⟨p.val.1, LinearMap.mem_ker.mpr (by
    change (A - B).mulVec p.val.1 = 0
    rw [Matrix.sub_mulVec, sub_eq_zero]
    exact p.property.1.symm.trans p.property.2)⟩
  left_inv _ := rfl
  right_inv p := Subtype.ext (Prod.ext rfl p.property.1.symm)
  map_add' x y := Subtype.ext (Prod.ext rfl (map_add _ _ _))
  map_smul' s x := Subtype.ext (Prod.ext rfl (map_smul _ _ _))

private theorem graph_intersection_finrank {F : Type*} [Field F]
    (A B : Matrix (Fin 5) (Fin 5) F) :
    Module.finrank F ↥(A.mulVecLin.graph ⊓ B.mulVecLin.graph) = 5 - (A - B).rank := by
  rw [← (graphInfKer A B).finrank_eq]
  have h := (A - B).mulVecLin.finrank_range_add_finrank_ker
  change (A - B).rank + _ = Module.finrank F (FiveSpace F) at h
  have hDimension : Module.finrank F (FiveSpace F) = 5 := by simp [FiveSpace]
  omega

private theorem sum_fin_five {M : Type*} [AddCommMonoid M] (f : Fin 5 → M) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + f 4))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

private theorem alternating_dot_mulVec {F : Type*} [Field F]
    {A : Matrix (Fin 5) (Fin 5) F} (h : IsAlternatingFive A) (x : FiveSpace F) :
    x ⬝ᵥ (A.mulVec x) = 0 := by
  simp only [Matrix.mulVec, dotProduct, sum_fin_five]
  rw [h.1 0, h.1 1, h.1 2, h.1 3, h.1 4, h.2 1 0, h.2 2 0, h.2 3 0, h.2 4 0,
    h.2 2 1, h.2 3 1, h.2 4 1, h.2 3 2, h.2 4 2, h.2 4 3]
  ring

private def halfSpinRootSpace (F : Type*) [Field F] : Submodule F (FiveSpace F × FiveSpace F) :=
  (0 : Matrix (Fin 5) (Fin 5) F).mulVecLin.graph

/-- Totally singular five-spaces in the half containing the horizontal
five-space. Odd intersection dimension specifies that half. -/
abbrev HalfSpinFiveVertex (F : Type*) [Field F] :=
  {U : Submodule F (FiveSpace F × FiveSpace F) //
    Module.finrank F U = 5 ∧ (∀ z ∈ U, z.1 ⬝ᵥ z.2 = 0) ∧
      Module.finrank F ↥(U ⊓ halfSpinRootSpace F) % 2 = 1}

/-- The hyperbolic half-spin graph in dimension ten. -/
def halfSpinFiveGraph (F : Type*) [Field F] : SimpleGraph (HalfSpinFiveVertex F) where
  Adj U W := Module.finrank F ↥(U.val ⊓ W.val) = 3
  symm := by
    constructor
    intro x y h
    change Module.finrank F ↥(x.val ⊓ y.val) = 3 at h
    rwa [inf_comm]
  loopless := by
    constructor
    intro U h
    change Module.finrank F ↥(U.val ⊓ U.val) = 3 at h
    rw [inf_idem, U.property.1] at h
    contradiction

private def chartPointSpace {F : Type*} [Field F] (A : HalfSpinChartVertex F) :
    HalfSpinFiveVertex F :=
  ⟨A.val.mulVecLin.graph, by
    refine ⟨?_, ?_, ?_⟩
    · have h := graph_intersection_finrank A.val A.val
      rw [inf_idem, sub_self, Matrix.rank_zero, Nat.sub_zero] at h
      exact h
    · intro z hz
      rw [LinearMap.mem_graph_iff] at hz
      rw [hz]
      exact alternating_dot_mulVec A.property.1 z.1
    · have hRank : A.val.rank ≤ 5 := Matrix.rank_le_width A.val
      have hEven := A.property.2
      rw [halfSpinRootSpace, graph_intersection_finrank, sub_zero]
      omega⟩

private theorem graph_map_injective {F : Type*} [Field F]
    {A B : Matrix (Fin 5) (Fin 5) F} (h : A.mulVecLin.graph = B.mulVecLin.graph) :
    A = B := by
  ext i j
  let x : Fin 5 → F := Pi.single j 1
  have ha : (x, A.mulVecLin x) ∈ A.mulVecLin.graph := rfl
  rw [h, LinearMap.mem_graph_iff] at ha
  have hij := congrFun ha i
  simpa only [x, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hij

/-- The alternating chart is induced in the actual graph of five-spaces.
The rank condition comes from the dimension of the intersection of two
graphs of linear maps. -/
def halfSpinChartIntoGeometry (F : Type*) [Field F] :
    halfSpinChartGraph F ↪g halfSpinFiveGraph F where
  toFun := chartPointSpace
  inj' := fun _ _ h => Subtype.ext (graph_map_injective (congrArg Subtype.val h))
  map_rel_iff' := by
    intro A B
    change Module.finrank F ↥(A.val.mulVecLin.graph ⊓ B.val.mulVecLin.graph) = 3 ↔
      (A.val - B.val).rank = 2
    rw [graph_intersection_finrank]
    omega

end EPPAIII.Primitive
