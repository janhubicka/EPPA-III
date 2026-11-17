import EPPAIII.Primitive.GrassmannGraph
import EPPAIII.Primitive.BilinearConstituentObstructions

/-! # An induced pentagon in the second Grassmann constituent -/

namespace EPPAIII.Primitive

open Module Matrix

private theorem finrank_graph_inf {F X Y : Type*} [Field F]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y]
    (f g : X →ₗ[F] Y) :
    finrank F (f.graph ⊓ g.graph : Submodule F (X × Y)) = finrank F (LinearMap.ker (f - g)) := by
  let K := LinearMap.ker (f - g)
  let l : K →ₗ[F] X × Y := (LinearMap.id.prod f).comp K.subtype
  have hrange : LinearMap.range l = f.graph ⊓ g.graph := by
    ext ⟨x, y⟩
    change (∃ a : K, (a.val, f a.val) = (x, y)) ↔ y = f x ∧ y = g x
    constructor
    · rintro ⟨a, h⟩
      have ha : f a.val - g a.val = 0 := a.property
      have hx : a.val = x := congrArg Prod.fst h
      have hy : f a.val = y := congrArg Prod.snd h
      rw [hx] at ha hy
      exact ⟨hy.symm, hy.symm.trans (sub_eq_zero.mp ha)⟩
    · rintro ⟨hf, hg⟩
      refine ⟨⟨x, ?_⟩, Prod.ext rfl hf.symm⟩
      exact sub_eq_zero.mpr (hf.symm.trans hg)
  have hinj : Function.Injective l := by
    intro a b h
    exact Subtype.ext (congrArg Prod.fst h)
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]

private theorem finrank_graph {F X Y : Type*} [Field F] [AddCommGroup X]
    [Module F X] [AddCommGroup Y] [Module F Y] (f : X →ₗ[F] Y) :
    finrank F f.graph = finrank F X := by
  rw [LinearMap.graph_eq_range_prod]
  exact LinearMap.finrank_range_of_inj (fun _ _ h => congrArg Prod.fst h)

private theorem finrank_ker_vecMulLinear {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) :
    A.rank + finrank F (LinearMap.ker A.vecMulLinear) = 2 := by
  rw [← Matrix.rank_transpose A, Matrix.rank, Matrix.mulVecLin_transpose]
  simpa using A.vecMulLinear.finrank_range_add_finrank_ker

private theorem vecMulLinear_sub {F : Type*} [Field F] {m : ℕ}
    (A B : Matrix (Fin 2) (Fin m) F) :
    (A - B).vecMulLinear = A.vecMulLinear - B.vecMulLinear :=
  (Matrix.toLinearMapRight' (R := F)).map_sub A B

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- Graphs of the rank-two bilinear maps give the induced pentagon in the
   distinct nonneighbours of the root. -/
noncomputable def grassmannGraph_nonlocal_fiveCycle
    (root : GrassmannPlane F V) (hDim : 5 ≤ finrank F V) :
    SimpleGraph.cycleGraph 5 ↪g (grassmannGraph F V).induce
      {Q | root ≠ Q ∧ ¬ (grassmannGraph F V).Adj root Q} := by
  classical
  let W := (Submodule.exists_isCompl root.val).choose
  have hW : IsCompl root.val W := (Submodule.exists_isCompl root.val).choose_spec
  let m := finrank F W
  let raw := root.val.prodEquivOfIsCompl W hW
  have hm : 3 ≤ m := by
    have h := raw.finrank_eq
    rw [Module.finrank_prod, root.property] at h
    change 2 + m = finrank F V at h
    omega
  let e₁ : (Fin 2 → F) ≃ₗ[F] root.val := LinearEquiv.ofFinrankEq _ _ (by simp [root.property])
  let e₂ : (Fin m → F) ≃ₗ[F] W := LinearEquiv.ofFinrankEq _ _ (by simp [m])
  let e := (e₁.prodCongr e₂).trans raw
  let P (A : Matrix (Fin 2) (Fin m) F) : GrassmannPlane F V :=
    ⟨A.vecMulLinear.graph.map e.toLinearMap, by rw [e.finrank_map_eq, finrank_graph]; simp⟩
  have hRoot : P 0 = root := by
    apply Subtype.ext
    change (0 : Matrix (Fin 2) (Fin m) F).vecMulLinear.graph.map e.toLinearMap = root.val
    ext x
    constructor
    · rintro ⟨⟨u, v⟩, huv, rfl⟩
      have hv : v = 0 := by
        change v = (0 : Matrix (Fin 2) (Fin m) F).vecMulLinear u at huv
        simpa using huv
      subst v
      simp [e, raw, Submodule.coe_prodEquivOfIsCompl']
    · intro hx
      refine ⟨(e₁.symm ⟨x, hx⟩, 0), ?_, ?_⟩
      · simp [LinearMap.mem_graph_iff]
      · simp [e, raw, Submodule.coe_prodEquivOfIsCompl']
  have hIntersection (A B : Matrix (Fin 2) (Fin m) F) :
      (A - B).rank + finrank F ((P A).val ⊓ (P B).val : Submodule F V) = 2 := by
    change _ + finrank F (A.vecMulLinear.graph.map e.toLinearMap ⊓ B.vecMulLinear.graph.map e.toLinearMap : Submodule F V) = _
    rw [← Submodule.map_inf _ e.injective, e.finrank_map_eq, finrank_graph_inf,
      ← vecMulLinear_sub]
    exact finrank_ker_vecMulLinear (A - B)
  have hAdj (A B : Matrix (Fin 2) (Fin m) F) :
      (grassmannGraph F V).Adj (P A) (P B) ↔ (A - B).rank = 1 := by
    have h := hIntersection A B
    change finrank F ((P A).val ⊓ (P B).val : Submodule F V) = 1 ↔ _
    omega
  have hInj : Function.Injective P := by
    intro A B h
    have hg : A.vecMulLinear.graph = B.vecMulLinear.graph :=
      Submodule.map_injective_of_injective e.injective (congrArg Subtype.val h)
    apply (Matrix.toLinearMapRight' (R := F)).injective
    apply LinearMap.ext
    intro u
    have hv : (u, A.vecMulLinear u) ∈ B.vecMulLinear.graph := hg ▸ (by
      change A.vecMulLinear u = A.vecMulLinear u
      rfl)
    exact (LinearMap.mem_graph_iff _ _).mp hv
  let f (A : BilinearRankTwo F m) :
      {Q : GrassmannPlane F V // root ≠ Q ∧ ¬ (grassmannGraph F V).Adj root Q} := by
    refine ⟨P A.val, ?_, ?_⟩
    · rw [← hRoot]
      exact fun h => ((bilinearFormsGraph_zero_nonadj_iff A.val).mpr A.property).1
        (hInj h).symm
    · rw [← hRoot, hAdj]
      intro h
      exact ((bilinearFormsGraph_zero_nonadj_iff A.val).mpr A.property).2 h
  have he : bilinearFormsRankTwoGraph F m ↪g (grassmannGraph F V).induce
      {Q | root ≠ Q ∧ ¬ (grassmannGraph F V).Adj root Q} :=
    ⟨⟨f, fun _ _ h => Subtype.ext (hInj (congrArg Subtype.val h))⟩,
      fun {A B} => hAdj A.val B.val⟩
  exact he.comp (bilinearRankTwo_fiveCycle hm)

end EPPAIII.Primitive
