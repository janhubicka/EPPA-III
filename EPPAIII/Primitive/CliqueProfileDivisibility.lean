import EPPAIII.Primitive.AffineMatchingExclusion
import Mathlib.Algebra.BigOperators.Fin

/-! # Full stabilizer divisibility from the sizes of selected local cliques -/

namespace EPPAIII.Primitive

open SimpleGraph
open scoped BigOperators

private noncomputable def cliqueFibreSize {U : Type*} {s : ℕ} (part : U → Fin s) (i : Fin s) : ℕ :=
  Nat.card {x // part x = i}

private abbrev CliqueLayer {U : Type*} {s Q : ℕ} (part : U → Fin s) (j : Fin Q) :=
  {i : Fin s // cliqueFibreSize part i = j.val + 1}

private abbrev LayeredVertex {U : Type*} {s Q : ℕ} (part : U → Fin s) :=
  Σ j : Fin Q, CliqueLayer part j × Fin (j.val + 1)

private theorem cliqueLayer_eq_of_index_eq {U : Type*} {s Q : ℕ} {part : U → Fin s}
    {j k : Fin Q} {i : CliqueLayer part j} {i' : CliqueLayer part k}
    (h : i.val = i'.val) : j = k := by
  apply Fin.ext
  have hi := i.property
  have hi' := i'.property
  rw [h, hi'] at hi
  omega

private def layeredCliqueGraph {U : Type*} {s Q : ℕ} (part : U → Fin s) :
    SimpleGraph (LayeredVertex (Q := Q) part) where
  Adj x y := x.2.1.val = y.2.1.val ∧ x ≠ y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private noncomputable def fibreLabel {U : Type*} {s Q : ℕ} [Finite U] {part : U → Fin s} {j : Fin Q}
    (i : CliqueLayer part j) : {x // part x = i.val} ≃ Fin (j.val + 1) :=
  Finite.equivFinOfCardEq i.property

private theorem labelledVertex_eq {U : Type*} {s Q : ℕ} [Finite U] {part : U → Fin s}
    {j k : Fin Q} {i : CliqueLayer part j} {i' : CliqueLayer part k}
    {x : {u // part u = i.val}} {x' : {u // part u = i'.val}}
    (hj : j = k) (hi : i.val = i'.val) (hx : x.val = x'.val) :
    (⟨j, i, fibreLabel i x⟩ : LayeredVertex part) = ⟨k, i', fibreLabel i' x'⟩ := by
  subst k
  have hIndex : i = i' := Subtype.ext hi
  subst i'
  have hVertex : x = x' := Subtype.ext hx
  subst x'
  rfl

private noncomputable def layeredLabel {U : Type*} {s Q : ℕ} [Finite U] (part : U → Fin s)
    (hCap : ∀ i, cliqueFibreSize part i ≤ Q) : U ≃ LayeredVertex (Q := Q) part := by
  have hPos (x : U) : 0 < cliqueFibreSize part (part x) := Nat.card_pos_iff.mpr
    ⟨⟨⟨x, rfl⟩⟩, inferInstance⟩
  let index (x : U) : Fin Q := ⟨cliqueFibreSize part (part x) - 1, by
    have h := hCap (part x)
    have hx := hPos x
    omega⟩
  let subtype (x : U) : CliqueLayer part (index x) := ⟨part x, by
    have hx := hPos x
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

private def cliqueLayerGraph {U : Type*} {s Q : ℕ} (part : U → Fin s) (j : Fin Q) :
    SimpleGraph (CliqueLayer part j × Fin (j.val + 1)) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private theorem layerGraph_card_automorphisms {U : Type*} {s Q : ℕ}
    (part : U → Fin s) (j : Fin Q) :
    Nat.card (graphAutomorphisms (cliqueLayerGraph part j)) =
      (Nat.card (CliqueLayer part j)).factorial *
        (j.val + 1).factorial ^ Nat.card (CliqueLayer part j) := by
  classical
  let φ : cliqueLayerGraph part j ≃g
      cliqueUnion (Nat.card (CliqueLayer part j)) (j.val + 1) :=
    ⟨(Finite.equivFin (CliqueLayer part j)).prodCongr (Equiv.refl _), by
      intro x y
      change (_ = _ ∧ x.2 ≠ y.2) ↔ x.1 = y.1 ∧ x.2 ≠ y.2
      exact and_congr (Finite.equivFin (CliqueLayer part j)).injective.eq_iff Iff.rfl⟩
  rw [card_automorphisms_of_iso φ, card_automorphisms_cliqueUnion (Nat.zero_lt_succ _)]

private theorem sameLayer_adj_iff {U : Type*} {s Q : ℕ} {part : U → Fin s}
    (j : Fin Q) (x y : CliqueLayer part j × Fin (j.val + 1)) :
    (layeredCliqueGraph part).Adj ⟨j, x⟩ ⟨j, y⟩ ↔ (cliqueLayerGraph part j).Adj x y := by
  change x.1.val = y.1.val ∧ (⟨j, x⟩ : LayeredVertex part) ≠ ⟨j, y⟩ ↔
    x.1 = y.1 ∧ x.2 ≠ y.2
  constructor
  · rintro ⟨h, hNe⟩
    have hi : x.1 = y.1 := Subtype.ext h
    exact ⟨hi, fun hc => hNe (congrArg (Sigma.mk j) (Prod.ext hi hc))⟩
  · rintro ⟨h, hNe⟩
    refine ⟨congrArg Subtype.val h, fun he => hNe ?_⟩
    exact congrArg Prod.snd (eq_of_heq (Sigma.mk.inj_iff.mp he).2)

private theorem differentLayer_not_adj {U : Type*} {s Q : ℕ} {part : U → Fin s}
    {j k : Fin Q} (h : j ≠ k) (x : CliqueLayer part j × Fin (j.val + 1))
    (y : CliqueLayer part k × Fin (k.val + 1)) :
    ¬ (layeredCliqueGraph part).Adj ⟨j, x⟩ ⟨k, y⟩ :=
  fun hAdj => h (cliqueLayer_eq_of_index_eq hAdj.1)

private def layeredAutos {U : Type*} {s Q : ℕ} (part : U → Fin s) :
    (∀ j : Fin Q, graphAutomorphisms (cliqueLayerGraph part j)) →*
      graphAutomorphisms (layeredCliqueGraph (Q := Q) part) where
  toFun p := ⟨Equiv.sigmaCongrRight fun j => (p j).val, by
    rintro ⟨j, x⟩ ⟨k, y⟩
    by_cases h : j = k
    · subst k
      change (layeredCliqueGraph part).Adj ⟨j, x⟩ ⟨j, y⟩ ↔
        (layeredCliqueGraph part).Adj ⟨j, (p j).val x⟩ ⟨j, (p j).val y⟩
      rw [sameLayer_adj_iff, sameLayer_adj_iff]
      exact (p j).property x y
    · exact iff_of_false (differentLayer_not_adj h x y)
        (differentLayer_not_adj h ((p j).val x) ((p k).val y))⟩
  map_one' := Subtype.ext (Equiv.ext (by rintro ⟨j, x⟩; rfl))
  map_mul' p q := Subtype.ext (Equiv.ext (by rintro ⟨j, x⟩; rfl))

private theorem layeredAutos_injective {U : Type*} {s Q : ℕ} (part : U → Fin s) :
    Function.Injective (layeredAutos (Q := Q) part) := by
  intro p q he
  funext j
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hin := congrArg (fun f : graphAutomorphisms (layeredCliqueGraph (Q := Q) part) =>
    f.val ⟨j, x⟩) he
  exact eq_of_heq (Sigma.mk.inj_iff.mp hin).2

private theorem cliqueLayers_count {U : Type*} {s Q : ℕ} [Finite U]
    (part : U → Fin s) (hCap : ∀ i, cliqueFibreSize part i ≤ Q) :
    (∑ j : Fin Q, Nat.card (CliqueLayer part j)) ≤ s ∧
    (∑ j : Fin Q, Nat.card (CliqueLayer part j) * (j.val + 1)) = Nat.card U := by
  let f : (Σ j : Fin Q, CliqueLayer part j) → Fin s := fun x => x.2.val
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

set_option maxHeartbeats 2000000 in
/-- The exact-size clique layers give a product of wreath-product groups
inside the automorphism group of the selected local graph. The local EPPA
section transfers its order to the full host point stabilizer. -/
theorem local_cliqueProfile_order_dvd_root_stabilizer
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) {s Q : ℕ}
    (φ : localGraph H (e root) ≃g cliqueUnion s Q) :
    ∃ m : Fin Q → ℕ, (∑ j, m j) ≤ s ∧
      (∑ j, m j * (j.val + 1)) = Nat.card (G.neighborSet root) ∧
      (∏ j, (j.val + 1).factorial ^ m j * (m j).factorial) ∣
        Nat.card (pointwiseGraphStabilizer H {e root}) := by
  classical
  let eLoc : localGraph G root ↪g localGraph H (e root) :=
    ⟨⟨fun x => ⟨e x, (heppa.1 root x).mp x.property⟩,
        fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩,
      fun {x y} => (heppa.1 x y).symm⟩
  let k := φ.toEmbedding.comp eLoc
  let part : G.neighborSet root → Fin s := fun x => (k x).1
  have hCap (i : Fin s) : cliqueFibreSize part i ≤ Q := by
    let idx (x : {u // part u = i}) : Fin Q := (k x.val).2
    have hi : Function.Injective idx := by
      intro x y h
      apply Subtype.ext
      apply k.injective
      exact Prod.ext (x.property.trans y.property.symm) h
    have hb := Nat.card_le_card_of_injective idx hi
    simpa only [cliqueFibreSize, Nat.card_fin] using hb
  let m (j : Fin Q) := Nat.card (CliqueLayer part j)
  obtain ⟨hCount, hWeight⟩ := cliqueLayers_count part hCap
  refine ⟨m, hCount, hWeight, ?_⟩
  let L := layeredLabel part hCap
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
  let ψ : localGraph G root ≃g layeredCliqueGraph (Q := Q) part :=
    ⟨L, fun {x y} => (and_congr Iff.rfl (not_congr L.injective.eq_iff)).trans (hAdj x y).symm⟩
  have hLayerDiv := Subgroup.card_dvd_of_injective (layeredAutos (Q := Q) part) (layeredAutos_injective part)
  have hRootDiv := automorphisms_dvd_root_stabilizer_of_local_embedding G H e heppa root
    ψ.symm.toEmbedding
  simpa only [Nat.card_pi, layerGraph_card_automorphisms, m, mul_comm] using hLayerDiv.trans hRootDiv

end EPPAIII.Primitive
