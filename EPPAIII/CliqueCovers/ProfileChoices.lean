import Mathlib

/-!
# Counting independent partial-coordinate assignments

Given s clique indices and t vertices per clique, choose r indices
and then independently choose a k-subset of Fin t at each selected
index. The exact number of such choices is

  (s.choose r) * (t.choose k)^r.

This is the finite combinatorial parameter space used to construct a
family of distinct profiles in the wreath-product orbit of a given
profile. The present theorem counts the parameter space; it does not
claim these choices have yet been injected into the actual orbit.
-/

namespace EPPAIII.CliqueCovers

/-- A size-r choice of clique positions together with a size-k
subset in each selected position. Each dependent second coordinate
is defined only on the selected positions, as with Finset.pi. -/
noncomputable def profileChoiceSpace (s t r k : ℕ) :
    Finset (Σ R : Finset (Fin s), ∀ i : Fin s, i ∈ R → Finset (Fin t)) := by
  classical
  exact
    ((Finset.univ : Finset (Fin s)).powersetCard r).sigma
      (fun R =>
        R.pi (fun _ => (Finset.univ : Finset (Fin t)).powersetCard k))

/-- Exact count of position choices and independent k-subset
choices. Valid even if k>t or r>s (both sides vanish). -/
theorem profileChoiceSpace_card (s t r k : ℕ) :
    (profileChoiceSpace s t r k).card =
      (Nat.choose s r) * (Nat.choose t k)^r := by
  classical
  unfold profileChoiceSpace
  rw [Finset.card_sigma]
  have hEach (R : Finset (Fin s))
      (hR : R ∈ (Finset.univ : Finset (Fin s)).powersetCard r) :
      (R.pi (fun _ => (Finset.univ : Finset (Fin t)).powersetCard k)).card =
        (Nat.choose t k)^r := by
    rw [Finset.card_pi]
    simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_const]
    have hcard : R.card = r := (Finset.mem_powersetCard.mp hR).2
    rw [hcard]
  calc
    (∑ R ∈ (Finset.univ : Finset (Fin s)).powersetCard r,
      (R.pi (fun _ =>
        (Finset.univ : Finset (Fin t)).powersetCard k)).card)
        = ∑ _R ∈ (Finset.univ : Finset (Fin s)).powersetCard r,
            (Nat.choose t k)^r := by
          apply Finset.sum_congr rfl
          intro R hR
          exact hEach R hR
    _ = ((Finset.univ : Finset (Fin s)).powersetCard r).card *
          (Nat.choose t k)^r := by simp
    _ = (Nat.choose s r) * (Nat.choose t k)^r := by
          simp [Finset.card_powersetCard]

/-- Membership conditions for a concrete independent assignment,
in terms of the selected positions and coordinate set sizes. -/
theorem mem_profileChoiceSpace_iff (s t r k : ℕ)
    (R : Finset (Fin s))
    (A : ∀ i : Fin s, i ∈ R → Finset (Fin t)) :
    (⟨R,A⟩ : Σ R : Finset (Fin s),
      ∀ i : Fin s, i ∈ R → Finset (Fin t)) ∈
        profileChoiceSpace s t r k ↔
      R.card = r ∧ ∀ i (hi : i ∈ R), (A i hi).card = k := by
  classical
  simp [profileChoiceSpace, Finset.mem_sigma, Finset.mem_pi,
    Finset.mem_powersetCard]

end EPPAIII.CliqueCovers
