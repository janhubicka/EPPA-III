import EPPAIII.Primitive.NeighbourhoodBound
import Mathlib.FieldTheory.Fixed
import Mathlib.Tactic.Ring

/-! # Two selected anchors in a one-dimensional affine semilinear host -/

namespace EPPAIII.Primitive

/-- Each profile into selected anchors fits in one orbit of their pointwise
stabilizer. Count profiles and orbit points independently. -/
theorem card_le_pow_mul_add_of_pointwise_stabilizer {V W : Type*}
    [Fintype V] [Finite W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (U : Finset V) :
    Fintype.card V ≤ 2 ^ U.card *
      Nat.card {q : Equiv.Perm W //
        IsGraphAutomorphism H q ∧ ∀ u ∈ U, q (e u) = e u} + U.card := by
  classical
  let S : Type _ := ↥Uᶜ
  let Q := {q : Equiv.Perm W //
    IsGraphAutomorphism H q ∧ ∀ u ∈ U, q (e u) = e u}
  let profile : S → (↥U → Bool) := fun x u => decide (G.Adj x u)
  let tag (x : S) : Set.range profile := ⟨profile x, x, rfl⟩
  let representative (p : Set.range profile) : S := p.property.choose
  have hRep (x : S) : profile (representative (tag x)) = profile x :=
    (tag x).property.choose_spec
  have hMoves (x : S) : ∃ q : Q, q.val (e (representative (tag x))) = e x := by
    obtain ⟨q, hq, hMap, hFix⟩ :=
      eppa_same_profile_extension G H e heppa U (representative (tag x)) x
        (Finset.mem_compl.mp (representative (tag x)).property)
        (Finset.mem_compl.mp x.property) (by
          intro u hu
          exact decide_eq_decide.mp (congrFun (hRep x) (⟨u, hu⟩ : ↥U)))
    exact ⟨⟨q, hq, hFix⟩, hMap⟩
  let encode (x : S) : (↥U → Bool) × Q := (profile x, (hMoves x).choose)
  have hInj : Function.Injective encode := by
    intro x y h
    have hTag : tag x = tag y := Subtype.ext (congrArg Prod.fst h)
    have hQ : (hMoves x).choose = (hMoves y).choose := congrArg Prod.snd h
    apply Subtype.ext
    apply e.injective
    calc
      e x = (hMoves x).choose.val (e (representative (tag x))) := (hMoves x).choose_spec.symm
      _ = (hMoves y).choose.val (e (representative (tag y))) :=
        congrArg₂ (fun (q : Q) (p : Set.range profile) => q.val (e (representative p))) hQ hTag
      _ = e y := (hMoves y).choose_spec
  have hCard := Nat.card_le_card_of_injective encode hInj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := S),
    Nat.card_eq_fintype_card (α := ↥U → Bool),
    Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_coe] at hCard
  have hSplit := Finset.card_compl_add_card U
  change Fintype.card V ≤ 2 ^ U.card * Nat.card Q + U.card
  omega

/-- An affine semilinear map fixing two distinct points is determined by its
field automorphism. The formula uses affine coordinates based at those points. -/
theorem affineLine_apply_of_fixed_pair {K F : Type*}
    [Field K] [Field F] [Algebra K F]
    (q : Equiv.Perm F) (a b : F) (σ : F ≃ₐ[K] F)
    (hq : ∀ z, q z = a * σ z + b)
    (x y : F) (hxy : x ≠ y) (hx : q x = x) (hy : q y = y) (z : F) :
    q z = x + (y - x) * σ ((z - x) / (y - x)) := by
  have hDiff (s t : F) : q s - q t = a * σ (s - t) := by
    rw [hq s, hq t, map_sub]
    ring
  have hDelta : a * σ (y - x) = y - x := by
    rw [← hDiff y x, hx, hy]
  have hDecomp : (y - x) * ((z - x) / (y - x)) = z - x := by
    rw [mul_comm (y - x), div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.symm)]
  calc
    q z = x + (q z - x) := by ring
    _ = x + a * σ (z - x) := by rw [← hDiff z x, hx]
    _ = x + (a * σ (y - x)) * σ ((z - x) / (y - x)) := by
      rw [mul_assoc, ← map_mul, hDecomp]
    _ = x + (y - x) * σ ((z - x) / (y - x)) :=
      congrArg (fun c => x + c * σ ((z - x) / (y - x))) hDelta

/-- A fixed induced selection in a semilinear affine-line host has order at
most four times the base field extension degree, plus the two anchors. The
full host action containment is an explicit input. -/
theorem affineLine_eppa_order_bound {V K F : Type*}
    [Fintype V] [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (heppa : IsEPPAEmbedding G H e)
    (hAffine : ∀ q : Equiv.Perm F, IsGraphAutomorphism H q →
      ∃ a b : F, ∃ σ : F ≃ₐ[K] F, ∀ z, q z = a * σ z + b) :
    Fintype.card V ≤ 4 * Module.finrank K F + 2 := by
  classical
  by_cases hSmall : Fintype.card V ≤ 1
  · omega
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  let U : Finset V := {x, y}
  let Q := {q : Equiv.Perm F //
    IsGraphAutomorphism H q ∧ ∀ u ∈ U, q (e u) = e u}
  have hRep (q : Q) : ∃ a b : F, ∃ σ : F ≃ₐ[K] F, ∀ z, q.val z = a * σ z + b :=
    hAffine q.val q.property.1
  choose a b σ hσ using hRep
  have hCode : Function.Injective σ := by
    intro q q' hEq
    apply Subtype.ext
    apply Equiv.ext
    intro z
    have hx (t : Q) : t.val (e x) = e x := t.property.2 x (by simp [U])
    have hy (t : Q) : t.val (e y) = e y := t.property.2 y (by simp [U])
    rw [affineLine_apply_of_fixed_pair q.val (a q) (b q) (σ q) (hσ q) (e x) (e y)
      (e.injective.ne hxy) (hx q) (hy q),
      affineLine_apply_of_fixed_pair q'.val (a q') (b q') (σ q') (hσ q') (e x) (e y)
        (e.injective.ne hxy) (hx q') (hy q'), hEq]
  have hGal := Nat.card_le_card_of_injective σ hCode
  rw [Nat.card_eq_fintype_card (α := F ≃ₐ[K] F)] at hGal
  have hQ : Nat.card Q ≤ Module.finrank K F := hGal.trans AlgEquiv.card_le
  have hU : U.card = 2 := by simp [U, hxy]
  calc
    Fintype.card V ≤ 2 ^ U.card * Nat.card Q + U.card :=
      card_le_pow_mul_add_of_pointwise_stabilizer G H e heppa U
    _ ≤ 4 * Module.finrank K F + 2 := by
      rw [hU]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 hQ) 2

end EPPAIII.Primitive
