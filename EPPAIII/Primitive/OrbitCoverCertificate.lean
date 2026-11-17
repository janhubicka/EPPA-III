import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

/-!
# Completeness of a finite orbit cover certificate

A survivor at the next level is a one-point extension of some earlier
survivor, up to the permitted permutations. Completeness does not depend
on the permutations generating the full symmetry group.
-/

namespace EPPAIII.Primitive

/-- Every set satisfying the hereditary property is carried by a permitted
permutation to a representative of its size. Only one-point extensions of
previous representatives need to be covered. -/
theorem good_maps_to_orbit_level {W : Type*} [DecidableEq W]
    (Good : Finset W → Prop) (permitted : Equiv.Perm W → Prop)
    (reps : ℕ → Set (Finset W)) (last : ℕ)
    (empty_mem : ∅ ∈ reps 0)
    (erase_good : ∀ S, Good S → ∀ x, Good (S.erase x))
    (map_good : ∀ S, Good S → ∀ q, permitted q → Good (S.map q.toEmbedding))
    (refl_permitted : permitted (Equiv.refl W))
    (trans_permitted : ∀ q r, permitted q → permitted r → permitted (q.trans r))
    (extend_covered : ∀ n < last, ∀ R ∈ reps n, ∀ x ∉ R, Good (insert x R) →
      ∃ q, permitted q ∧ (insert x R).map q.toEmbedding ∈ reps (n + 1))
    : ∀ n ≤ last, ∀ S : Finset W, S.card = n → Good S →
      ∃ q, permitted q ∧ S.map q.toEmbedding ∈ reps n := by
  intro n
  induction n with
  | zero =>
      intro _ S hCard _
      have hEmpty := Finset.card_eq_zero.mp hCard
      exact ⟨Equiv.refl W, refl_permitted, by simpa [hEmpty] using empty_mem⟩
  | succ n ih =>
      intro hLast S hCard hGood
      obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      have hErase : (S.erase x).card = n := by
        rw [Finset.card_erase_of_mem hx, hCard]
        omega
      obtain ⟨q, hq, hR⟩ := ih (by omega) _ hErase (erase_good S hGood x)
      let R := (S.erase x).map q.toEmbedding
      have hNotMem : q x ∉ R := by
        simp [R]
      have hImage : S.map q.toEmbedding = insert (q x) R := by
        simpa only [R, Finset.insert_erase hx, Equiv.coe_toEmbedding] using
          (Finset.map_insert q.toEmbedding x (S.erase x))
      have hGoodR : Good (insert (q x) R) := hImage ▸ map_good S hGood q hq
      obtain ⟨r, hr, hNext⟩ :=
        extend_covered n (by omega) R hR (q x) hNotMem hGoodR
      refine ⟨q.trans r, trans_permitted q r hq hr, ?_⟩
      rw [← hImage, Finset.map_map] at hNext
      exact hNext

/-- An empty layer proves that every set of that size fails the property. -/
theorem no_good_of_empty_orbit_level {W : Type*} [DecidableEq W]
    (Good : Finset W → Prop) (permitted : Equiv.Perm W → Prop)
    (reps : ℕ → Set (Finset W)) (last : ℕ)
    (empty_mem : ∅ ∈ reps 0)
    (erase_good : ∀ S, Good S → ∀ x, Good (S.erase x))
    (map_good : ∀ S, Good S → ∀ q, permitted q → Good (S.map q.toEmbedding))
    (refl_permitted : permitted (Equiv.refl W))
    (trans_permitted : ∀ q r, permitted q → permitted r → permitted (q.trans r))
    (extend_covered : ∀ n < last, ∀ R ∈ reps n, ∀ x ∉ R, Good (insert x R) →
      ∃ q, permitted q ∧ (insert x R).map q.toEmbedding ∈ reps (n + 1))
    (last_empty : reps last = ∅) :
    ∀ S : Finset W, S.card = last → ¬ Good S := by
  intro S hCard hGood
  obtain ⟨q, _, hMem⟩ := good_maps_to_orbit_level Good permitted reps last
    empty_mem erase_good map_good refl_permitted trans_permitted extend_covered
    last le_rfl S hCard hGood
  simp [last_empty] at hMem

end EPPAIII.Primitive
