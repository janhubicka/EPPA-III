import EPPAIII.Primitive.AffineLineArithmetic
import EPPAIII.Primitive.AffineLineBound
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Half-order exclusions from the action of an affine-line host -/

namespace EPPAIII.Primitive

/-- Every host automorphism is affine semilinear over the given base field. -/
def HasAffineLineAction (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]
    (H : SimpleGraph F) : Prop :=
  ∀ q : Equiv.Perm F, IsGraphAutomorphism H q →
    ∃ a b : F, ∃ σ : F ≃ₐ[K] F, ∀ z, q z = a * σ z + b

/-- Double the two-anchor bound for a selected copy of at least half the host. -/
theorem affineLine_host_order_bound {V K F : Type*}
    [Finite V] [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (heppa : IsEPPAEmbedding G H e) (hLarge : Nat.card F ≤ 2 * Nat.card V)
    (hAffine : HasAffineLineAction K H) :
    Nat.card F ≤ 8 * Module.finrank K F + 4 := by
  classical
  let := Fintype.ofFinite V
  have hOrder := affineLine_eppa_order_bound G H e heppa hAffine
  rw [Nat.card_eq_fintype_card (α := V)] at hLarge
  omega

/-- The full semilinear action and Paley arithmetic leave orders five and nine. -/
theorem affineLine_paley_host_orders {V K F : Type*}
    [Finite V] [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (heppa : IsEPPAEmbedding G H e) (hLarge : Nat.card F ≤ 2 * Nat.card V)
    (hAffine : HasAffineLineAction K H) {p : ℕ} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4)
    (hr : 0 < Module.finrank K F) (hCard : Nat.card F = p ^ Module.finrank K F)
    (hPaley : Nat.card F % 4 = 1) : Nat.card F = 5 ∨ Nat.card F = 9 := by
  have hBound := affineLine_host_order_bound G H e heppa hLarge hAffine
  rw [hCard] at hBound hPaley ⊢
  exact affineLine_paley_small_orders hp₂ hp₄ hr hBound hPaley

/-- The full semilinear action and Peisert arithmetic leave order nine. -/
theorem affineLine_peisert_host_order {V K F : Type*}
    [Finite V] [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (heppa : IsEPPAEmbedding G H e) (hLarge : Nat.card F ≤ 2 * Nat.card V)
    (hAffine : HasAffineLineAction K H) {p : ℕ} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4)
    (hr : 0 < Module.finrank K F) (hCard : Nat.card F = p ^ Module.finrank K F)
    (hPrime : p % 4 = 3) (hEven : Module.finrank K F % 2 = 0) : Nat.card F = 9 := by
  have hBound := affineLine_host_order_bound G H e heppa hLarge hAffine
  rw [hCard] at hBound ⊢
  exact affineLine_peisert_small_orders hp₂ hp₄ hr hBound hPrime hEven

/-- The full semilinear action and Van Lint–Schrijver arithmetic leave the
listed field orders and connection indices. -/
theorem affineLine_vanLintSchrijver_host_orders {V K F : Type*}
    [Finite V] [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (heppa : IsEPPAEmbedding G H e) (hLarge : Nat.card F ≤ 2 * Nat.card V)
    (hAffine : HasAffineLineAction K H) {p ℓ : ℕ} (hp₂ : 2 ≤ p) (hp₄ : p ≠ 4)
    (hr : 0 < Module.finrank K F) (hCard : Nat.card F = p ^ Module.finrank K F)
    (hOdd : ℓ % 2 = 1) (hIndexLarge : 2 < ℓ) (hIndex : ℓ ∣ Nat.card F - 1)
    (hOrder : ℓ - 1 ∣ Module.finrank K F) :
    (Nat.card F = 4 ∧ ℓ = 3) ∨ (Nat.card F = 16 ∧ (ℓ = 3 ∨ ℓ = 5)) := by
  have hBound := affineLine_host_order_bound G H e heppa hLarge hAffine
  rw [hCard] at hBound hIndex ⊢
  exact affineLine_vanLintSchrijver_small_orders hp₂ hp₄ hr hBound hOdd hIndexLarge hIndex hOrder

/-- The connected strongly regular parameter equation eliminates the
order-four and the degree-three order-sixteen Van Lint–Schrijver rows. Here
`hPositive` is positivity of the common-neighbor number for a nonedge. -/
theorem vanLintSchrijver_order_sixteen_of_connected_parameters {n ℓ k l μ : ℕ}
    (hCases : (n = 4 ∧ ℓ = 3) ∨ (n = 16 ∧ (ℓ = 3 ∨ ℓ = 5)))
    (hDegree : k * ℓ = n - 1) (hPositive : 0 < μ)
    (hParameters : k * (k - l - 1) = (n - k - 1) * μ) : n = 16 ∧ ℓ = 3 := by
  rcases hCases with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
  · have hk : k = 1 := by omega
    subst k
    omega
  · exact ⟨rfl, rfl⟩
  · have hk : k = 3 := by omega
    subst k
    have hUpper : 3 * (3 - l - 1) ≤ 6 := by omega
    omega

/-- The full host automorphisms fixing a set pointwise. -/
def hostPointwiseStabilizer {W : Type*} (H : SimpleGraph W) (A : Set W) :
    Subgroup (Equiv.Perm W) where
  carrier := {q | IsGraphAutomorphism H q ∧ ∀ a ∈ A, q a = a}
  one_mem' := ⟨fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro q r ⟨hq, hqFix⟩ ⟨hr, hrFix⟩
    exact ⟨fun x y => (hr x y).trans (hq (r x) (r y)),
      fun a ha => by rw [Equiv.Perm.mul_apply, hrFix a ha, hqFix a ha]⟩
  inv_mem' := by
    rintro q ⟨hq, hqFix⟩
    refine ⟨fun x y => ?_, fun a ha => ?_⟩
    · change H.Adj x y ↔ H.Adj (q.symm x) (q.symm y)
      simpa using (hq (q.symm x) (q.symm y)).symm
    · change q.symm a = a
      simpa using congrArg q.symm (hqFix a ha).symm

/-- A uniform bound on the host's two-point stabilizers bounds every selected copy. -/
theorem eppa_order_le_of_pair_stabilizers {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) {k : ℕ}
    (hPair : ∀ x y : W, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ k) :
    Nat.card V ≤ 4 * k + 2 := by
  classical
  let := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  by_cases hSmall : Fintype.card V ≤ 1
  · omega
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  let U : Finset V := {x, y}
  let Q := {q : Equiv.Perm W // IsGraphAutomorphism H q ∧ ∀ u ∈ U, q (e u) = e u}
  have hFix (q : Equiv.Perm W) : q ∈ hostPointwiseStabilizer H {e x, e y} ↔
      IsGraphAutomorphism H q ∧ ∀ u ∈ U, q (e u) = e u := by
    change (IsGraphAutomorphism H q ∧ ∀ a ∈ ({e x, e y} : Set W), q a = a) ↔ _
    simp [U]
  have hCard : Nat.card Q ≤ k :=
    (Nat.card_congr (Equiv.subtypeEquivRight hFix)).symm.le.trans (hPair _ _ (e.injective.ne hxy))
  have hBound := card_le_pow_mul_add_of_pointwise_stabilizer G H e heppa U
  have hU : U.card = 2 := by simp [U, hxy]
  rw [hU] at hBound
  exact hBound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hCard) 2)

/-- A pair-stabilizer bound excludes a copy of at least half the host when the
host order exceeds twice the resulting upper bound. This includes the
order-49 and order-529 entries with stabilizer bounds three and one. -/
theorem not_eppa_embedding_of_pair_stabilizers {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hLarge : Nat.card W ≤ 2 * Nat.card V) {k : ℕ} (hOrder : 8 * k + 4 < Nat.card W)
    (hPair : ∀ x y : W, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ k) :
    ¬ IsEPPAEmbedding G H e := by
  intro heppa
  have hBound := eppa_order_le_of_pair_stabilizers G H e heppa hPair
  omega

/-- If every two-point stabilizer has order at most twelve, a selected copy
has at most twenty-six vertices. A larger copy has an adjacency profile of
size at least seven into two anchors. The corresponding orbit forces its
point stabilizer to be trivial, so a third anchor gives the bound eleven. -/
theorem eppa_order_le_twentySix_of_pair_stabilizers {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hPair : ∀ x y : W, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ 12) :
    Nat.card V ≤ 26 := by
  classical
  let := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card]
  by_contra! hLarge
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne V
  let U : Finset V := {x, y}
  let S : Type _ := ↥Uᶜ
  let Q := hostPointwiseStabilizer H {e x, e y}
  let profile : S → (↥U → Bool) := fun v u => decide (G.Adj v u)
  have hU : U.card = 2 := by simp [U, hxy]
  have hSplit := Finset.card_compl_add_card U
  have hProfiles : Fintype.card (↥U → Bool) = 4 := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hU]
    decide
  have hOutside : 24 < Fintype.card S := by
    change 24 < Fintype.card (↥Uᶜ : Type _)
    rw [Fintype.card_coe]
    omega
  obtain ⟨tag, hTag⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card profile
    (n := 6) (by rw [hProfiles]; exact hOutside)
  let C : Finset S := Finset.univ.filter (fun v => profile v = tag)
  change 6 < C.card at hTag
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
  have hOutsideU (v : S) : (v : V) ∉ U := Finset.mem_compl.mp v.property
  have hMem (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
      (hFix : ∀ u ∈ U, q (e u) = e u) : q ∈ Q := by
    change IsGraphAutomorphism H q ∧ ∀ a ∈ ({e x, e y} : Set W), q a = a
    refine ⟨hq, ?_⟩
    rintro a (rfl | rfl)
    · exact hFix x (by simp [U])
    · exact hFix y (by simp [U])
  have hMoves (w : C) : e (w.val : V) ∈ MulAction.orbit Q (e (z : V)) := by
    have hProfile (v : S) (hv : v ∈ C) : profile v = tag :=
      (Finset.mem_filter.mp hv).2
    have hEq := (hProfile z hz).trans (hProfile w.val w.property).symm
    obtain ⟨q, hq, hMove, hFix⟩ := eppa_same_profile_extension G H e heppa U
      (z : V) (w.val : V) (hOutsideU z) (hOutsideU w.val) (by
        intro u hu
        exact decide_eq_decide.mp (congrFun hEq (⟨u, hu⟩ : ↥U)))
    exact ⟨⟨q, hMem q hq hFix⟩, hMove⟩
  let O := MulAction.orbit Q (e (z : V))
  let T := MulAction.stabilizer Q (e (z : V))
  let encode : C → O := fun w => ⟨e (w.val : V), hMoves w⟩
  have hEncode : Function.Injective encode := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (e.injective (congrArg Subtype.val hab)))
  have hOrb := Nat.card_le_card_of_injective encode hEncode
  rw [Nat.card_eq_fintype_card (α := ↥C), Fintype.card_coe] at hOrb
  have hProduct : Nat.card O * Nat.card T = Nat.card Q := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q (e (z : V)))
  have hQ : Nat.card Q ≤ 12 := hPair _ _ (e.injective.ne hxy)
  have hTCard : Nat.card T = 1 := by
    have hPos : 0 < Nat.card T := Nat.card_pos
    by_contra hNotOne
    have hMul := Nat.mul_le_mul_left (Nat.card O) (show 2 ≤ Nat.card T by omega)
    omega
  let : Subsingleton T := (Nat.card_eq_one_iff_unique.mp hTCard).1
  let A := insert (z : V) U
  have hA : A.card = 3 := by
    change (insert (z : V) U).card = 3
    rw [Finset.card_insert_of_notMem (hOutsideU z), hU]
  have hBound := card_le_pow_add_of_pointwise_fixation G H e heppa A (by
    intro q hq hFix v
    let qQ : Q := ⟨q, hMem q hq (fun u hu => hFix u (Finset.mem_insert_of_mem hu))⟩
    have hInT : qQ ∈ T := hFix z (by simp [A])
    have hId : (⟨qQ, hInT⟩ : T) = 1 := Subsingleton.elim _ _
    have hPerm : q = 1 := congrArg (fun r : T => r.val.val) hId
    rw [hPerm, Equiv.Perm.one_apply])
  rw [hA] at hBound
  omega

/-- The pair stabilizer bound rules out the exceptional order-81 Peisert
host once its full two-point stabilizers are known to have order at most twelve. -/
theorem not_eppa_embedding_order_eightyOne_of_pair_stabilizers {V W : Type*}
    [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hLarge : Nat.card W ≤ 2 * Nat.card V) (hOrder : Nat.card W = 81)
    (hPair : ∀ x y : W, x ≠ y → Nat.card (hostPointwiseStabilizer H {x, y}) ≤ 12) :
    ¬ IsEPPAEmbedding G H e := by
  intro heppa
  have hBound := eppa_order_le_twentySix_of_pair_stabilizers G H e heppa hPair
  omega

end EPPAIII.Primitive
