import EPPAIII.Primitive.LocalSections

/-!
# Factorial divisibility in the host point stabilizer
-/

namespace EPPAIII.Primitive

variable {V W : Type*}

/-- A selected clique or independent set whose vertices have the same adjacency
profiles into the anchors forces a factorial divisor in the host pointwise stabilizer. -/
theorem factorial_dvd_pointwiseStabilizer_card_of_homogeneous_subset [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (U : Finset V) (S : Set V)
    (hOutside : ∀ u ∈ U, u ∉ S)
    (hConst : ∀ u ∈ U, ∀ x ∈ S, ∀ y ∈ S, G.Adj u x ↔ G.Adj u y)
    (hHomogeneous : G.induce S = ⊤ ∨ G.induce S = ⊥)
    {n : Nat} (hSize : n ≤ Nat.card S) :
    n.factorial ∣ Nat.card (pointwiseGraphStabilizer H (e '' (U : Set V))) := by
  classical
  let := Fintype.ofFinite S
  have hAll (p : Equiv.Perm S) : IsGraphAutomorphism (G.induce S) p := by
    rcases hHomogeneous with hComplete | hEmpty
    · rw [hComplete]
      intro x y
      change x ≠ y ↔ p x ≠ p y
      exact ⟨p.injective.ne, fun h hEq => h (congrArg p hEq)⟩
    · rw [hEmpty]
      intro x y
      rfl
  let allPerms : graphAutomorphisms (G.induce S) ≃ Equiv.Perm S := {
    toFun p := p.val
    invFun p := ⟨p, hAll p⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hCard : Nat.card (graphAutomorphisms (G.induce S)) = (Nat.card S).factorial := by
    rw [Nat.card_congr allPerms, Nat.card_eq_fintype_card, Fintype.card_perm,
      ← Nat.card_eq_fintype_card]
  have hSurj := restrictToSelected_surjective G H e heppa S U hOutside
    (fun p u hu x => hConst u hu x x.property (p.val x) (p.val x).property)
  have hGroupDiv := Subgroup.card_dvd_of_surjective hSurj
  have hStabilizerDiv :=
    (setwiseGraphStabilizer H (e '' (U : Set V))
      (Set.range ((Function.Embedding.subtype (· ∈ S)).trans e))).card_subgroup_dvd_card
  rw [hCard] at hGroupDiv
  exact (Nat.factorial_dvd_factorial hSize).trans (hGroupDiv.trans hStabilizerDiv)

/-- A clique or independent set in an actual selected subconstituent
forces a factorial divisor in the host point stabilizer. -/
theorem factorial_dvd_rootStabilizer_card_of_homogeneous_subset [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (S : Set V)
    (hOutside : root ∉ S)
    (hConst : ∀ x ∈ S, ∀ y ∈ S, G.Adj root x ↔ G.Adj root y)
    (hHomogeneous : G.induce S = ⊤ ∨ G.induce S = ⊥)
    {n : Nat} (hSize : n ≤ Nat.card S) :
    n.factorial ∣ Nat.card (pointwiseGraphStabilizer H {e root}) := by
  simpa only [Finset.coe_singleton, Set.image_singleton] using
    factorial_dvd_pointwiseStabilizer_card_of_homogeneous_subset G H e heppa {root} S
      (fun u hu => (Finset.mem_singleton.mp hu).symm ▸ hOutside)
      (fun u hu => (Finset.mem_singleton.mp hu).symm ▸ hConst) hHomogeneous hSize

end EPPAIII.Primitive
