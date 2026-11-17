import EPPAIII.Primitive.PolarRankTwoExclusion
import EPPAIII.Primitive.UnitaryFiveTwoArithmetic
import Mathlib.Algebra.BigOperators.Fin

/-! # The 165-vertex unitary quadrangle -/

namespace EPPAIII.Primitive

open SimpleGraph
open scoped BigOperators

private noncomputable def cliqueFibreSize {U : Type*} (part : U → Fin 9) (i : Fin 9) : ℕ :=
  Nat.card {x // part x = i}

private abbrev CliqueLayer {U : Type*} (part : U → Fin 9) (j : Fin 4) :=
  {i : Fin 9 // cliqueFibreSize part i = j.val + 1}

private abbrev LayeredVertex {U : Type*} (part : U → Fin 9) :=
  Σ j : Fin 4, CliqueLayer part j × Fin (j.val + 1)

private abbrev LayeredPermutations {U : Type*} (part : U → Fin 9) :=
  ∀ j : Fin 4, Equiv.Perm (CliqueLayer part j) ×
    (CliqueLayer part j → Equiv.Perm (Fin (j.val + 1)))

private theorem cliqueLayer_eq_of_index_eq {U : Type*} {part : U → Fin 9}
    {j k : Fin 4} {i : CliqueLayer part j} {i' : CliqueLayer part k}
    (h : i.val = i'.val) : j = k := by
  apply Fin.ext
  have hi := i.property
  have hi' := i'.property
  rw [h, hi'] at hi
  omega

private def layeredCliqueGraph {U : Type*} (part : U → Fin 9) :
    SimpleGraph (LayeredVertex part) where
  Adj x y := x.2.1.val = y.2.1.val ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private def layerPerm {I : Type*} {m : ℕ}
    (σ : Equiv.Perm I) (ρ : I → Equiv.Perm (Fin m)) : Equiv.Perm (I × Fin m) where
  toFun x := (σ x.1, ρ x.1 x.2)
  invFun x := (σ.symm x.1, (ρ (σ.symm x.1)).symm x.2)
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp

private def layeredPerm {U : Type*} {part : U → Fin 9} (p : LayeredPermutations part) :
    Equiv.Perm (LayeredVertex part) :=
  Equiv.sigmaCongrRight fun j => layerPerm (p j).1 (p j).2

private theorem layeredPerm_automorphism {U : Type*} {part : U → Fin 9}
    (p : LayeredPermutations part) :
    IsGraphAutomorphism (layeredCliqueGraph part) (layeredPerm p) := by
  intro x y
  have hIndex : x.2.1.val = y.2.1.val ↔ (layeredPerm p x).2.1.val = (layeredPerm p y).2.1.val := by
    rcases x with ⟨j, i, a⟩
    rcases y with ⟨k, i', a'⟩
    change i.val = i'.val ↔ ((p j).1 i).val = ((p k).1 i').val
    constructor
    · intro h
      have hjk := cliqueLayer_eq_of_index_eq h
      subst k
      exact congrArg Subtype.val (congrArg (p j).1 (Subtype.ext h))
    · intro h
      have hjk := cliqueLayer_eq_of_index_eq h
      subst k
      exact congrArg Subtype.val ((p j).1.injective (Subtype.ext h))
  exact and_congr hIndex (not_congr (layeredPerm p).injective.eq_iff.symm)

private theorem layeredPerm_injective {U : Type*} {part : U → Fin 9} :
    Function.Injective (layeredPerm (part := part)) := by
  intro p q h
  funext j
  have hPair (i : CliqueLayer part j) (a : Fin (j.val + 1)) :
      ((p j).1 i, (p j).2 i a) = ((q j).1 i, (q j).2 i a) := by
    have hAt := DFunLike.congr_fun h (⟨j, i, a⟩ : LayeredVertex part)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hAt).2
  apply Prod.ext
  · apply Equiv.ext
    intro i
    exact congrArg Prod.fst (hPair i ⟨0, Nat.zero_lt_succ _⟩)
  · funext i
    apply Equiv.ext
    intro a
    exact congrArg Prod.snd (hPair i a)

private noncomputable def fibreLabel {U : Type*} [Finite U] {part : U → Fin 9} {j : Fin 4}
    (i : CliqueLayer part j) : {x // part x = i.val} ≃ Fin (j.val + 1) :=
  Finite.equivFinOfCardEq i.property

private theorem labelledVertex_eq {U : Type*} [Finite U] {part : U → Fin 9}
    {j k : Fin 4} {i : CliqueLayer part j} {i' : CliqueLayer part k}
    {x : {u // part u = i.val}} {x' : {u // part u = i'.val}}
    (hj : j = k) (hi : i.val = i'.val) (hx : x.val = x'.val) :
    (⟨j, i, fibreLabel i x⟩ : LayeredVertex part) = ⟨k, i', fibreLabel i' x'⟩ := by
  subst k
  have hIndex : i = i' := Subtype.ext hi
  subst i'
  have hVertex : x = x' := Subtype.ext hx
  subst x'
  rfl

private noncomputable def layeredLabel {U : Type*} [Finite U] (part : U → Fin 9)
    (hCap : ∀ i, cliqueFibreSize part i ≤ 4) : U ≃ LayeredVertex part := by
  let index (x : U) : Fin 4 := ⟨cliqueFibreSize part (part x) - 1, by
    have h := hCap (part x)
    omega⟩
  let subtype (x : U) : CliqueLayer part (index x) := ⟨part x, by
    have hPos : 0 < cliqueFibreSize part (part x) := Nat.card_pos_iff.mpr
      ⟨⟨⟨x, rfl⟩⟩, inferInstance⟩
    change cliqueFibreSize part (part x) = (cliqueFibreSize part (part x) - 1) + 1
    omega⟩
  refine
    { toFun := fun x => ⟨index x, subtype x, fibreLabel (subtype x) ⟨x, rfl⟩⟩
      invFun := fun x => ((fibreLabel x.2.1).symm x.2.2).val
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    exact congrArg Subtype.val ((fibreLabel (subtype x)).symm_apply_apply ⟨x, rfl⟩)
  · rintro ⟨j, i, a⟩
    let x := (fibreLabel i).symm a
    change (⟨index x.val, subtype x.val, fibreLabel (subtype x.val) ⟨x.val, rfl⟩⟩ :
        LayeredVertex part) = ⟨j, i, a⟩
    have hj : index x.val = j := cliqueLayer_eq_of_index_eq (i := subtype x.val) (i' := i) x.property
    have h := labelledVertex_eq (i := subtype x.val) (x := ⟨x.val, rfl⟩) (x' := x) hj x.property rfl
    simpa only [x, Equiv.apply_symm_apply] using h

private theorem succ_zero_fin_four : (0 : Fin 3).succ = (1 : Fin 4) := rfl
private theorem succ_succ_zero_fin_four : (0 : Fin 2).succ.succ = (2 : Fin 4) := rfl
private theorem succ_succ_succ_zero_fin_four : (0 : Fin 1).succ.succ.succ = (3 : Fin 4) := rfl

private theorem layeredPermutations_card {U : Type*} (part : U → Fin 9) :
    Nat.card (LayeredPermutations part) =
      fourCliqueSizesAutOrder (Nat.card (CliqueLayer part 0)) (Nat.card (CliqueLayer part 1))
        (Nat.card (CliqueLayer part 2)) (Nat.card (CliqueLayer part 3)) := by
  classical
  simp only [LayeredPermutations, Nat.card_pi, Nat.card_prod, Nat.card_fin,
    Nat.card_perm, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, fourCliqueSizesAutOrder]
  simp only [succ_zero_fin_four, succ_succ_zero_fin_four, succ_succ_succ_zero_fin_four]
  norm_num [Nat.factorial]
  ring

private theorem cliqueLayers_count {U : Type*} [Finite U] (part : U → Fin 9)
    (hCap : ∀ i, cliqueFibreSize part i ≤ 4) :
    (∑ j : Fin 4, Nat.card (CliqueLayer part j)) ≤ 9 ∧
    (∑ j : Fin 4, Nat.card (CliqueLayer part j) * (j.val + 1)) = Nat.card U := by
  let f : (Σ j : Fin 4, CliqueLayer part j) → Fin 9 := fun x => x.2.val
  have hf : Function.Injective f := by
    rintro ⟨j, i⟩ ⟨k, i'⟩ h
    have hjk : j = k := cliqueLayer_eq_of_index_eq (i := i) (i' := i') h
    subst k
    exact congrArg (Sigma.mk j) (Subtype.ext h)
  have hSize := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sigma, Nat.card_fin] at hSize
  refine ⟨hSize, ?_⟩
  have hSize' := Nat.card_congr (layeredLabel part hCap).symm
  simpa only [LayeredVertex, Nat.card_sigma, Nat.card_prod, Nat.card_fin] using hSize'

private theorem unitaryFiveTwo_card_automorphisms_of_cliques {U : Type*} [Finite U]
    (J : SimpleGraph U) (part : U → Fin 9) (hCap : ∀ i, cliqueFibreSize part i ≤ 4)
    (hAdj : ∀ x y, J.Adj x y ↔ part x = part y ∧ x ≠ y)
    (hSize : 19 ≤ Nat.card U) :
    497664 ≤ Nat.card (graphAutomorphisms J) := by
  classical
  let φ := layeredLabel part hCap
  have hMap (x y : U) : J.Adj x y ↔ (layeredCliqueGraph part).Adj (φ x) (φ y) :=
    (hAdj x y).trans (and_congr Iff.rfl (not_congr φ.injective.eq_iff.symm))
  let transport (p : LayeredPermutations part) : graphAutomorphisms J :=
    ⟨(φ.trans (layeredPerm p)).trans φ.symm, by
      intro x y
      exact (hMap x y).trans ((layeredPerm_automorphism p (φ x) (φ y)).trans (by
        simpa only [Equiv.apply_symm_apply, Equiv.trans_apply] using
          (hMap (φ.symm (layeredPerm p (φ x))) (φ.symm (layeredPerm p (φ y)))).symm))⟩
  have hInj : Function.Injective transport := by
    intro p q h
    apply layeredPerm_injective
    apply Equiv.ext
    intro x
    have hAt := congrArg (fun a : graphAutomorphisms J => a.val (φ.symm x)) h
    simpa [transport] using congrArg φ hAt
  have hBound := Nat.card_le_card_of_injective transport hInj
  rw [layeredPermutations_card] at hBound
  obtain ⟨hCliques, hWeighted⟩ := cliqueLayers_count part hCap
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, succ_zero_fin_four,
    succ_succ_zero_fin_four, succ_succ_succ_zero_fin_four] at hCliques hWeighted
  apply (unitaryFiveTwo_cliqueProfileMin ?_ ?_).trans hBound
  · omega
  · rw [← hWeighted] at hSize
    rw [show (0 : Fin 4).val + 1 = 1 from rfl, show (1 : Fin 4).val + 1 = 2 from rfl,
      show (2 : Fin 4).val + 1 = 3 from rfl, show (3 : Fin 4).val + 1 = 4 from rfl,
      Nat.mul_one] at hSize
    omega

/-- The unitary point graph on 165 vertices is excluded by the selected
clique profile. The full point-stabilizer bound and graph data are
inputs from the rank-two unitary model. -/
theorem unitaryFiveTwo_point_not_eppa {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (root : V) (hSRG : H.IsSRGWith 165 36 3 9)
    (φ : localGraph H (e root) ≃g cliqueUnion 9 4)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) ≤ 165888) : False := by
  classical
  have hSmall : ¬ (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x}) := by
    intro hLarge
    have hRange : RankTwoPolarRange 4 8 := Or.inl ⟨by decide, by decide⟩
    obtain ⟨hClique, hCoClique, hCover, hCoCover⟩ :=
      polar_rankTwo_actual_second_constituent_excludes_forms H hRange hSRG (e root)
    rcases hShape hLarge with ⟨s, b, ⟨ψ⟩ | ⟨ψ⟩⟩ | ⟨s, b, X, Y, ⟨ψ⟩ | ⟨ψ⟩⟩
    · obtain ⟨ψ⟩ := ψ
      exact (hClique s b).false ψ
    · obtain ⟨ψ⟩ := ψ
      exact (hCoClique s b).false ψ
    · obtain ⟨ψ⟩ := ψ
      exact (hCover s b X Y).false ψ
    · obtain ⟨ψ⟩ := ψ
      exact (hCoCover s b X Y).false ψ
  have hHost : Nat.card W = 165 := Nat.card_eq_fintype_card.trans hSRG.card
  have hLocal : Nat.card (H.neighborSet (e root)) = 36 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr φ.toEquiv
  have hHostSplit := order_eq_one_add_subconstituent_orders H (e root)
  have hBaseSplit := order_eq_one_add_subconstituent_orders G root
  have hSize : 19 ≤ Nat.card (G.neighborSet root) := by omega
  let f : localGraph G root ↪g localGraph H (e root) :=
    ⟨⟨fun x => ⟨e x, (heppa.1 root x).mp x.property⟩,
        fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩,
      fun {x y} => (heppa.1 x y).symm⟩
  let k := φ.toEmbedding.comp f
  let part : G.neighborSet root → Fin 9 := fun x => (k x).1
  have hCap (i : Fin 9) : cliqueFibreSize part i ≤ 4 := by
    let idx (x : {u // part u = i}) : Fin 4 := (k x.val).2
    have hi : Function.Injective idx := by
      intro x y h
      apply Subtype.ext
      apply k.injective
      exact Prod.ext (x.property.trans y.property.symm) h
    have hb := Nat.card_le_card_of_injective idx hi
    simpa only [cliqueFibreSize, Nat.card_fin] using hb
  have hAdj (x y : G.neighborSet root) :
      (localGraph G root).Adj x y ↔ part x = part y ∧ x ≠ y := by
    have h := (k.map_rel_iff (a := x) (b := y)).symm
    change (localGraph G root).Adj x y ↔
      (k x).1 = (k y).1 ∧ (k x).2 ≠ (k y).2 at h
    refine h.trans (and_congr_right (fun hIndex => ⟨?_, ?_⟩))
    · intro hDifferent hEqual
      exact hDifferent (congrArg (fun a => (k a).2) hEqual)
    · intro hDifferent hEqual
      exact hDifferent (k.injective (Prod.ext hIndex hEqual))
  have hAuto := unitaryFiveTwo_card_automorphisms_of_cliques (localGraph G root) part hCap hAdj hSize
  have hSurj := root_restrictToSelected_surjective G H e heppa root (G.neighborSet root)
    (G.loopless.irrefl root) (fun _ hx _ hy => iff_of_true hx hy)
  have hSection := Nat.card_le_card_of_surjective _ hSurj
  have hInclusion (K : Subgroup (pointwiseGraphStabilizer H {e root})) :
      Nat.card K ≤ Nat.card (pointwiseGraphStabilizer H {e root}) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hBound := hAuto.trans (hSection.trans (hInclusion _))
  omega

end EPPAIII.Primitive
