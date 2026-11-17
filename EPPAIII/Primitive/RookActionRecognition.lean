import EPPAIII.Primitive.GraphTwoClosure
import EPPAIII.Primitive.RookModel

/-! # The orbital graph of the square product action -/

namespace EPPAIII.Primitive

private theorem perm_moves_pair {V : Type*} [DecidableEq V] (x y u v : V)
    (hStatus : x = y ↔ u = v) : ∃ p : Equiv.Perm V, p x = u ∧ p y = v := by
  by_cases hxy : x = y
  · subst y
    obtain rfl := hStatus.mp rfl
    exact ⟨Equiv.swap x u, Equiv.swap_apply_left x u, Equiv.swap_apply_left x u⟩
  · have huv : u ≠ v := fun h => hxy (hStatus.mpr h)
    let p := Equiv.swap x u
    have hpu : p x = u := Equiv.swap_apply_left x u
    have hpy : p y ≠ u := by
      rw [← hpu]
      exact p.injective.ne (Ne.symm hxy)
    refine ⟨p.trans (Equiv.swap (p y) v), ?_, Equiv.swap_apply_left (p y) v⟩
    rw [Equiv.trans_apply, hpu]
    exact Equiv.swap_apply_of_ne_of_ne hpy.symm huv

private theorem rookGraph_prod_action {n : ℕ} (p q : Equiv.Perm (Fin n)) :
    IsGraphAutomorphism (rookGraph n) (p.prodCongr q) := by
  intro x y
  change (x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)) ↔
    ((p.prodCongr q) x ≠ (p.prodCongr q) y ∧ (p x.1 = p y.1 ∨ q x.2 = q y.2))
  simp only [(p.prodCongr q).injective.ne_iff, p.injective.eq_iff, q.injective.eq_iff]

private theorem rookGraph_transpose_action {n : ℕ} :
    IsGraphAutomorphism (rookGraph n) (Equiv.prodComm (Fin n) (Fin n)) := by
  intro x y
  change (x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)) ↔
    ((Equiv.prodComm _ _) x ≠ (Equiv.prodComm _ _) y ∧ (x.2 = y.2 ∨ x.1 = y.1))
  simp only [(Equiv.prodComm (Fin n) (Fin n)).injective.ne_iff, or_comm]

/-- Invariance under independent coordinate permutations and transposition
gives the two orbital graphs of the square product action. -/
theorem graph_eq_rook_or_compl_of_product_action {n : ℕ} (hn : 2 ≤ n)
    (H : SimpleGraph (Fin n × Fin n))
    (hCoordinate : ∀ p q : Equiv.Perm (Fin n), IsGraphAutomorphism H (p.prodCongr q))
    (hTranspose : IsGraphAutomorphism H (Equiv.prodComm (Fin n) (Fin n)))
    (hEdge : ∃ x y, H.Adj x y) (hNonedge : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) :
    H = rookGraph n ∨ H = (rookGraph n)ᶜ := by
  classical
  let P := graphAutomorphisms (rookGraph n) ⊓ graphAutomorphisms H
  have hMove (x y u v : Fin n × Fin n)
      (h₁ : x.1 = y.1 ↔ u.1 = v.1) (h₂ : x.2 = y.2 ↔ u.2 = v.2) :
      ∃ p : P, p.val x = u ∧ p.val y = v := by
    obtain ⟨p, hpx, hpy⟩ := perm_moves_pair x.1 y.1 u.1 v.1 h₁
    obtain ⟨q, hqx, hqy⟩ := perm_moves_pair x.2 y.2 u.2 v.2 h₂
    exact ⟨⟨p.prodCongr q, rookGraph_prod_action p q, hCoordinate p q⟩,
      Prod.ext hpx hqx, Prod.ext hpy hqy⟩
  have hOrbits : HasRankThreeGraphOrbits P (rookGraph n) := by
    refine ⟨inf_le_left, ?_, ?_⟩
    · intro x u
      obtain ⟨p, hp, _⟩ := hMove x x u u (iff_of_true rfl rfl) (iff_of_true rfl rfl)
      exact ⟨p, hp⟩
    · intro x y u v hxy huv hAdj
      have hStatus : (x.1 = y.1 ∨ x.2 = y.2) ↔ (u.1 = v.1 ∨ u.2 = v.2) := by
        exact ⟨fun h => (hAdj.mp ⟨hxy, h⟩).2, fun h => (hAdj.mpr ⟨huv, h⟩).2⟩
      have hX : ¬ (x.1 = y.1 ∧ x.2 = y.2) := fun h => hxy (Prod.ext h.1 h.2)
      have hU : ¬ (u.1 = v.1 ∧ u.2 = v.2) := fun h => huv (Prod.ext h.1 h.2)
      have hAligned :
          ((x.1 = y.1 ↔ u.1 = v.1) ∧ (x.2 = y.2 ↔ u.2 = v.2)) ∨
          ((x.2 = y.2 ↔ u.1 = v.1) ∧ (x.1 = y.1 ↔ u.2 = v.2)) := by tauto
      rcases hAligned with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact hMove x y u v h₁ h₂
      · obtain ⟨p, hp, hq⟩ := hMove x.swap y.swap u v h₁ h₂
        let s : P := ⟨Equiv.prodComm _ _, rookGraph_transpose_action, hTranspose⟩
        exact ⟨p * s, hp, hq⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hRookEdge : ∃ x y, (rookGraph n).Adj x y :=
    ⟨(a, a), (a, b), by simp [rookGraph, hab]⟩
  have hRookNonedge : ∃ x y, x ≠ y ∧ ¬ (rookGraph n).Adj x y :=
    ⟨(a, a), (b, b), by simp [rookGraph, hab]⟩
  rcases hOrbits.invariant_graph_eq_or_compl inf_le_right hRookEdge hRookNonedge
      hEdge hNonedge with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [compl_compl] using congrArg (fun J => Jᶜ) h.symm)

/-- The product-action entry of the catalogue only needs containment of
the rank-three subgroup in the square wreath product. -/
theorem graph_eq_rook_or_compl_of_product_subgroup {n : ℕ} (hn : 2 ≤ n)
    {H : SimpleGraph (Fin n × Fin n)} {P : Subgroup (Equiv.Perm (Fin n × Fin n))}
    (hOrbits : HasRankThreeGraphOrbits P H)
    (hProduct : ∀ p : P, ∃ a b : Equiv.Perm (Fin n),
      p.val = a.prodCongr b ∨ p.val = (a.prodCongr b) * Equiv.prodComm _ _)
    (hEdge : ∃ x y, H.Adj x y) (hNonedge : ∃ x y, x ≠ y ∧ ¬ H.Adj x y) :
    H = rookGraph n ∨ H = (rookGraph n)ᶜ := by
  have hPreserve : P ≤ graphAutomorphisms (rookGraph n) := by
    intro p hp
    obtain ⟨a, b, h | h⟩ := hProduct ⟨p, hp⟩ <;> change p = _ at h
    · rw [h]
      exact rookGraph_prod_action a b
    · rw [h]
      apply (graphAutomorphisms (rookGraph n)).mul_mem
      · exact rookGraph_prod_action a b
      · exact rookGraph_transpose_action
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  exact hOrbits.invariant_graph_eq_or_compl hPreserve hEdge hNonedge
    ⟨(a, a), (a, b), by simp [rookGraph, hab]⟩
    ⟨(a, a), (b, b), by simp [rookGraph, hab]⟩

end EPPAIII.Primitive
