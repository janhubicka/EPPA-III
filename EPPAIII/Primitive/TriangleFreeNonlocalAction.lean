import EPPAIII.Primitive.PointStabilizerTransport
import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-! # Faithfulness on the nonlocal constituent of a triangle-free SRG -/

namespace EPPAIII.Primitive

private theorem neighbours_independent {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n k μ : ℕ}
    (hSRG : H.IsSRGWith n k 0 μ) {r a b : W} (ha : H.Adj r a) (hb : H.Adj r b) :
    ¬ H.Adj a b := by
  intro hab
  have hPos := Fintype.card_pos_iff.mpr
    (show Nonempty (H.commonNeighbors r a) from ⟨⟨b, H.mem_commonNeighbors.mpr ⟨hb, hab⟩⟩⟩)
  rw [hSRG.of_adj r a ha] at hPos
  exact (Nat.lt_irrefl 0) hPos

private theorem neighbour_eq_of_nonlocal_profile {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n k μ : ℕ}
    (hSRG : H.IsSRGWith n k 0 μ) (hStrict : μ < k) (r a b : W)
    (ha : H.Adj r a) (hb : H.Adj r b)
    (hProfile : ∀ x, r ≠ x ∧ ¬ H.Adj r x → (H.Adj a x ↔ H.Adj b x)) : a = b := by
  classical
  by_contra hne
  have hIncl (x : H.neighborSet a) : H.Adj b x := by
    by_cases hrx : r = x.val
    · rw [← hrx]
      exact hb.symm
    · exact (hProfile x ⟨hrx, fun hx => neighbours_independent H hSRG ha hx x.property⟩).mp
        x.property
  let f : H.neighborSet a ↪ H.commonNeighbors a b :=
    ⟨fun x => ⟨x.val, H.mem_commonNeighbors.mpr ⟨x.property, hIncl x⟩⟩,
      fun _ _ h => Subtype.ext (congrArg (fun z : H.commonNeighbors a b => z.val) h)⟩
  have hCard := Fintype.card_le_of_embedding f
  rw [H.card_neighborSet_eq_degree, hSRG.regular a,
    hSRG.of_not_adj hne (neighbours_independent H hSRG ha hb)] at hCard
  exact (Nat.not_le_of_lt hStrict) hCard

/-- When the nonadjacent codegree is strictly smaller than the degree,
the point stabilizer of a triangle-free SRG acts faithfully on its
second subconstituent. -/
theorem card_pointwiseGraphStabilizer_singleton_le_nonlocalAutomorphisms
    {W : Type*} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj] {n k μ : ℕ}
    (hSRG : H.IsSRGWith n k 0 μ) (hStrict : μ < k) (r : W) :
    Nat.card (pointwiseGraphStabilizer H {r}) ≤
      Nat.card (graphAutomorphisms (nonlocalGraph H r)) := by
  classical
  let P := hostPointwiseStabilizer H ({r} : Set W)
  have hFix (p : P) : p.val r = r := p.property.2 r (by simp)
  have hAdj (p : P) (x : W) : H.Adj r x ↔ H.Adj r (p.val x) := by
    simpa only [hFix p] using p.property.1 r x
  have hOutside (p : P) (x : W) :
      (r ≠ x ∧ ¬ H.Adj r x) ↔ (r ≠ p.val x ∧ ¬ H.Adj r (p.val x)) := by
    have hNe : p.val r ≠ p.val x ↔ r ≠ x := not_congr p.val.injective.eq_iff
    exact and_congr (by simpa only [hFix p] using hNe.symm) (not_congr (hAdj p x))
  let restrict (p : P) : graphAutomorphisms (nonlocalGraph H r) :=
    ⟨p.val.subtypeEquiv (hOutside p), fun x y => p.property.1 x y⟩
  have hInj : Function.Injective restrict := by
    intro p q he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    have hOn (a : W) (ha : r ≠ a ∧ ¬ H.Adj r a) : p.val a = q.val a :=
      congrArg (fun f : graphAutomorphisms (nonlocalGraph H r) => (f.val ⟨a, ha⟩).val) he
    by_cases hrx : r = x
    · subst x
      exact (hFix p).trans (hFix q).symm
    by_cases hx : H.Adj r x
    · apply neighbour_eq_of_nonlocal_profile H hSRG hStrict r _ _
        ((hAdj p x).mp hx) ((hAdj q x).mp hx)
      intro a ha
      obtain ⟨b, rfl⟩ := p.val.surjective a
      calc
        H.Adj (p.val x) (p.val b) ↔ H.Adj x b := (p.property.1 x b).symm
        _ ↔ H.Adj (q.val x) (q.val b) := q.property.1 x b
        _ ↔ H.Adj (q.val x) (p.val b) := by rw [hOn b ((hOutside p b).mpr ha)]
    · exact hOn x ⟨hrx, hx⟩
  rw [Nat.card_congr (pointwiseGraphStabilizerEquivHost H {r})]
  exact Nat.card_le_card_of_injective restrict hInj

end EPPAIII.Primitive
