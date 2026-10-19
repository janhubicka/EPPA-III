import Mathlib

/-!
# Parity of partial two-graph automorphisms

The Section 5.1 switching argument begins with a universal algebraic fact:
a symmetric edge discrepancy with zero parity on every triple is the
sum of one-vertex labels. These lemmas have no finite-size assumption.

This is a checked *component* of the proof of Lemma `lemma:gtg`, not a
claim that its cyclic and directed-path steps have already been formalized.
-/

namespace EPPAIII.TwoGraphs

/-- A symmetric two-point discrepancy with zero sum on every triple
is a difference of vertex labels over any abelian group of exponent two.
The extra argument `r` is a chosen anchor. -/
theorem triangle_discrepancy_potential_at
    {V A : Type*} [AddCommGroup A]
    (hTwo : ∀ a : A, a + a = 0)
    (δ : V → V → A)
    (hSym : ∀ x y, δ x y = δ y x)
    (hTriangle : ∀ x y z, δ x y + δ y z + δ z x = 0)
    (r : V) :
    ∃ h : V → A, ∀ x y, δ x y = h x + h y := by
  refine ⟨fun x => δ r x, ?_⟩
  intro x y
  have ht := hTriangle r x y
  rw [hSym y r] at ht
  calc
    δ x y = δ x y +
        ((δ r x + δ r x) + (δ r y + δ r y)) := by
      rw [hTwo (δ r x), hTwo (δ r y)]
      simp
    _ = (δ r x + δ x y + δ r y) +
        (δ r x + δ r y) := by abel
    _ = δ r x + δ r y := by rw [ht]; simp

/-- The empty-domain case is included. -/
theorem triangle_discrepancy_potential
    {V A : Type*} [AddCommGroup A]
    (hTwo : ∀ a : A, a + a = 0)
    (δ : V → V → A)
    (hSym : ∀ x y, δ x y = δ y x)
    (hTriangle : ∀ x y z, δ x y + δ y z + δ z x = 0) :
    ∃ h : V → A, ∀ x y, δ x y = h x + h y := by
  by_cases hn : Nonempty V
  · obtain ⟨r⟩ := hn
    exact triangle_discrepancy_potential_at hTwo δ hSym hTriangle r
  · refine ⟨fun _ => 0, ?_⟩
    intro x y
    exact (hn ⟨x⟩).elim

/-- If a partial injection preserves the parity on triples, the
discrepancy between an edge function and its pullback admits
a one-point potential. The injection's injectivity is not needed
for this preliminary algebraic step. -/
theorem partial_triple_parity_potential
    {V D A : Type*} [AddCommGroup A]
    (hTwo : ∀ a : A, a + a = 0)
    (e : V → V → A)
    (hSym : ∀ u v, e u v = e v u)
    (inc image : D → V)
    (hTriples : ∀ x y z : D,
      e (inc x) (inc y) + e (inc y) (inc z) +
          e (inc z) (inc x) =
      e (image x) (image y) + e (image y) (image z) +
          e (image z) (image x)) :
    ∃ h : D → A, ∀ x y : D,
      e (inc x) (inc y) + e (image x) (image y) =
        h x + h y := by
  let δ : D → D → A := fun x y =>
    e (inc x) (inc y) + e (image x) (image y)
  have hδSym : ∀ x y : D, δ x y = δ y x := by
    intro x y
    dsimp [δ]
    rw [hSym (inc x) (inc y), hSym (image x) (image y)]
  have hδTriangle : ∀ x y z : D,
      δ x y + δ y z + δ z x = 0 := by
    intro x y z
    calc
      δ x y + δ y z + δ z x =
          (e (inc x) (inc y) + e (inc y) (inc z) +
              e (inc z) (inc x)) +
          (e (image x) (image y) + e (image y) (image z) +
              e (image z) (image x)) := by
        dsimp [δ]
        abel
      _ = (e (image x) (image y) + e (image y) (image z) +
              e (image z) (image x)) +
          (e (image x) (image y) + e (image y) (image z) +
              e (image z) (image x)) := by
        rw [hTriples x y z]
      _ = 0 := hTwo _
  exact triangle_discrepancy_potential hTwo δ hδSym hδTriangle

end EPPAIII.TwoGraphs
