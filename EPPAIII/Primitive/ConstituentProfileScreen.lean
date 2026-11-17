import EPPAIII.Primitive.SparseConstituent

/-! # A finite order-and-degree screen for the Section 8 model forms -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The possible degrees of a cover with half-order `m` and clique size `t`.
The first four values have empty off-diagonal blocks and the last four
have full off-diagonal blocks. -/
def coverDegreesAtHalfOrder (m t : ℕ) : Finset ℕ :=
  {t - 1, t - 1 + t, t, t - 1 + (t - 1),
    m - 1, m - 1 + t, m, m - 1 + (t - 1)}

/-- A necessary numerical condition for a regular graph with order `n`
and degree `d` to be a generalized clique cover. -/
def CoverDegreeCompatible (n d : ℕ) : Prop :=
  n % 2 = 0 ∧ ∃ t : Fin (n / 2 + 1),
    0 < t.val ∧ t.val ∣ n / 2 ∧ d ∈ coverDegreesAtHalfOrder (n / 2) t.val

instance (n d : ℕ) : Decidable (CoverDegreeCompatible n d) := by
  unfold CoverDegreeCompatible
  infer_instance

/-- An isomorphism to a clique union forces degree plus one to divide the order. -/
theorem cliqueUnion_degree_dvd_order_of_iso {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n d : ℕ} (hn : 0 < n) (hCard : Fintype.card V = n)
    (hReg : G.IsRegularOfDegree d) {s t : ℕ} (φ : G ≃g cliqueUnion s t) :
    d + 1 ∣ n := by
  classical
  have hSize : Fintype.card (Fin s × Fin t) = n := φ.card_eq.symm.trans hCard
  have hProduct : s * t = n := by simpa using hSize
  obtain ⟨⟨i, a⟩⟩ := Fintype.card_pos_iff.mp (hSize.symm ▸ hn)
  have hDeg := φ.symm.degree_eq (i, a)
  rw [hReg, CliqueCovers.cliqueUnion_degree (i.isLt.pos)] at hDeg
  have ht : 0 < t := a.isLt.pos
  exact ⟨s, by rw [show d + 1 = t by omega, Nat.mul_comm, hProduct]⟩

/-- Every positive-order regular graph isomorphic to a generalized clique cover
satisfies the numerical screen. -/
theorem coverDegreeCompatible_of_iso {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n d : ℕ} (hn : 0 < n) (hCard : Fintype.card V = n)
    (hReg : G.IsRegularOfDegree d) {s t : ℕ} {X : CrossType} {Y : Bool}
    (φ : G ≃g coverGraph s t X Y) : CoverDegreeCompatible n d := by
  classical
  have hSize : Fintype.card (CoverVertex s t) = n := φ.card_eq.symm.trans hCard
  have hProduct : 2 * (s * t) = n := by
    simpa only [coverVertex_card, Nat.mul_assoc] using hSize
  obtain ⟨⟨_, i, a⟩⟩ := Fintype.card_pos_iff.mp (hSize.symm ▸ hn)
  have hs : 0 < s := i.isLt.pos
  have ht : 0 < t := a.isLt.pos
  have hHalf : s * t = n / 2 := by omega
  have hBound : t ≤ n / 2 := by
    simpa only [Nat.one_mul, hHalf] using Nat.mul_le_mul_right t (show 1 ≤ s by omega)
  have hDeg := φ.symm.degree_eq (left i a)
  rw [hReg, coverGraph_left_degree X Y i a] at hDeg
  have hOff : (s - 1) * t = n / 2 - t := by rw [Nat.sub_mul, Nat.one_mul, hHalf]
  have hDiv : t ∣ n / 2 := ⟨s, by rw [← hHalf, Nat.mul_comm]⟩
  refine ⟨by omega, ⟨t, by omega⟩, ht, hDiv, ?_⟩
  change d ∈ coverDegreesAtHalfOrder (n / 2) t
  cases X <;> cases Y <;>
    simp [coverDiagonalDegree, coverDegreesAtHalfOrder, hOff] at hDeg ⊢ <;> omega

private theorem model_degree_of_compl_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {M : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel M.Adj]
    {n d : ℕ} (hCard : Fintype.card V = n) (hReg : G.IsRegularOfDegree d)
    (φ : G ≃g Mᶜ) : M.IsRegularOfDegree (n - 1 - d) := by
  classical
  intro v
  have hSize := φ.card_eq.symm.trans hCard
  have hDeg := φ.symm.degree_eq v
  rw [hReg, degree_compl, hSize] at hDeg
  have hBound := M.degree_lt_card_verts v
  rw [hSize] at hBound
  omega

/-- A pair of divisibility tests excludes both orientations of a clique union. -/
theorem regular_profile_excludes_cliqueUnion {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n d : ℕ} (hn : 0 < n) (hd : d < n)
    (hCard : Fintype.card V = n) (hReg : G.IsRegularOfDegree d)
    (hDiv : ¬ (d + 1) ∣ n) (hDivCompl : ¬ (n - d) ∣ n) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) := by
  classical
  constructor
  · intro s t
    exact ⟨fun φ => hDiv (cliqueUnion_degree_dvd_order_of_iso hn hCard hReg φ)⟩
  · intro s t
    refine ⟨fun φ => ?_⟩
    have hD := cliqueUnion_degree_dvd_order_of_iso hn (φ.card_eq.symm.trans hCard)
      (model_degree_of_compl_iso hCard hReg φ) ((Iso.refl : cliqueUnion s t ≃g cliqueUnion s t))
    exact hDivCompl (by simpa only [show n - 1 - d + 1 = n - d by omega] using hD)

/-- Both cover orientations fail if neither the degree nor the complementary
degree passes the necessary finite-order screen. -/
theorem regular_profile_excludes_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n d : ℕ} (hn : 0 < n) (hCard : Fintype.card V = n)
    (hReg : G.IsRegularOfDegree d) (hCover : ¬ CoverDegreeCompatible n d)
    (hCoverCompl : ¬ CoverDegreeCompatible n (n - 1 - d)) :
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  constructor
  · intro s t X Y
    exact ⟨fun φ => hCover (coverDegreeCompatible_of_iso hn hCard hReg φ)⟩
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    exact hCoverCompl (coverDegreeCompatible_of_iso hn (φ.card_eq.symm.trans hCard)
      (model_degree_of_compl_iso hCard hReg φ) ((Iso.refl : coverGraph s t X Y ≃g coverGraph s t X Y)))

end EPPAIII.Primitive
