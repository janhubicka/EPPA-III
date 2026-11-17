import EPPAIII.Primitive.ClusterFactorialBound
import EPPAIII.Primitive.LocalSections
import EPPAIII.Primitive.Subconstituents
import Mathlib.Data.Finite.Perm

/-! # The product-factorial obstruction in a selected union of cliques -/

namespace EPPAIII.Primitive

open SimpleGraph
open scoped BigOperators

private def fibrePermutation {U I : Type*} (part : U → I)
    (p : ∀ i, Equiv.Perm {x // part x = i}) : Equiv.Perm U :=
  (Equiv.sigmaFiberEquiv part).symm.trans
    ((Equiv.sigmaCongrRight p).trans (Equiv.sigmaFiberEquiv part))

private theorem fibrePermutation_apply {U I : Type*} (part : U → I)
    (p : ∀ i, Equiv.Perm {x // part x = i}) (x : U) :
    fibrePermutation part p x = (p (part x) ⟨x, rfl⟩).val := rfl

private theorem product_factorials_le_cluster_automorphisms {U I : Type*} [Fintype I] [Finite U]
    (J : SimpleGraph U) (part : U → I)
    (hAdj : ∀ x y, J.Adj x y ↔ part x = part y ∧ x ≠ y) :
    (∏ i, (Nat.card {x // part x = i}).factorial) ≤ Nat.card (graphAutomorphisms J) := by
  let action (p : ∀ i, Equiv.Perm {x // part x = i}) : graphAutomorphisms J :=
    ⟨fibrePermutation part p, by
      have preserve (x : U) : part (fibrePermutation part p x) = part x :=
        (p (part x) ⟨x, rfl⟩).property
      intro x y
      rw [hAdj, hAdj, preserve, preserve]
      exact and_congr_right (fun _ => not_congr (fibrePermutation part p).injective.eq_iff.symm)⟩
  have hInjective : Function.Injective action := by
    intro p q hpq
    funext i
    apply Equiv.ext
    intro x
    apply Subtype.ext
    have h := congrArg (fun f : graphAutomorphisms J => f.val x.val) hpq
    change fibrePermutation part p x.val = fibrePermutation part q x.val at h
    rcases x with ⟨x, rfl⟩
    exact h
  have hBound := Nat.card_le_card_of_injective action hInjective
  rw [Nat.card_pi] at hBound
  simpa only [Nat.card_perm] using hBound

private theorem cluster_product_le_root_stabilizer
    {V W I : Type*} [Finite V] [Finite W] [Fintype I]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (root : V) (part : G.neighborSet root → I)
    (hAdj : ∀ x y, (localGraph G root).Adj x y ↔ part x = part y ∧ x ≠ y) :
    (∏ i, (Nat.card {x // part x = i}).factorial) ≤
      Nat.card (pointwiseGraphStabilizer H {e root}) := by
  classical
  have hAuto := product_factorials_le_cluster_automorphisms (localGraph G root) part hAdj
  have hSurj := root_restrictToSelected_surjective G H e heppa root (G.neighborSet root)
    (G.loopless.irrefl root) (fun _ hx _ hy => iff_of_true hx hy)
  have hSection := Nat.card_le_card_of_surjective _ hSurj
  have hInclusion (K : Subgroup (pointwiseGraphStabilizer H {e root})) :
      Nat.card K ≤ Nat.card (pointwiseGraphStabilizer H {e root}) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact hAuto.trans (hSection.trans (hInclusion _))

/-- If a sufficiently large selected neighbourhood is a union of cliques
with the given indexing, the ambient point stabilizer is at least as large
as the factorial of the average lower bound raised to the number of cliques.
Empty selected cliques may be included in the indexing. -/
theorem factorial_pow_le_root_stabilizer_of_clique_partition
    {V W I : Type*} [Finite V] [Finite W] [Fintype I]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (root : V) (part : G.neighborSet root → I)
    (hAdj : ∀ x y, (localGraph G root).Adj x y ↔ part x = part y ∧ x ≠ y)
    {m : ℕ} (hm : 0 < m) (hAvg : Fintype.card I * m ≤ Nat.card (G.neighborSet root)) :
    m.factorial ^ Fintype.card I ≤ Nat.card (pointwiseGraphStabilizer H {e root}) := by
  classical
  have hCount : (∑ i, Nat.card {x // part x = i}) = Nat.card (G.neighborSet root) := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv part)
  have hProd := factorial_pow_card_le_prod_of_average Finset.univ
    (fun i => Nat.card {x // part x = i}) hm (by simpa only [Finset.card_univ, hCount] using hAvg)
  rw [Finset.card_univ] at hProd
  exact hProd.trans (cluster_product_le_root_stabilizer G H e heppa root part hAdj)

private theorem selected_clique_partition
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (root : V) {s Q : ℕ} (φ : localGraph H (e root) ≃g cliqueUnion s Q) :
    ∃ part : G.neighborSet root → Fin s,
      ∀ x y, (localGraph G root).Adj x y ↔ part x = part y ∧ x ≠ y := by
  let f : localGraph G root ↪g localGraph H (e root) :=
    ⟨⟨fun x => ⟨e x, (heppa.1 root x).mp x.property⟩,
        fun _ _ h => Subtype.ext (e.injective (congrArg Subtype.val h))⟩,
      fun {x y} => (heppa.1 x y).symm⟩
  let k := φ.toEmbedding.comp f
  let part : G.neighborSet root → Fin s := fun x => (k x).1
  have hAdj (x y : G.neighborSet root) :
      (localGraph G root).Adj x y ↔ part x = part y ∧ x ≠ y := by
    have h := (k.map_rel_iff (a := x) (b := y)).symm
    change (localGraph G root).Adj x y ↔
      (k x).1 = (k y).1 ∧ (k x).2 ≠ (k y).2 at h
    refine h.trans (and_congr_right (fun hIndex => ⟨?_, ?_⟩))
    · intro hDifferent hEqual
      apply hDifferent
      exact congrArg (fun a => (k a).2) hEqual
    · intro hDifferent hEqual
      exact hDifferent (k.injective (Prod.ext hIndex hEqual))
  exact ⟨part, hAdj⟩

/-- A local model of equal cliques contributes one part per ambient clique
even if some of them miss the selected embedding. -/
theorem factorial_pow_le_root_stabilizer_of_local_clique_union
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (root : V) {s Q m : ℕ} (φ : localGraph H (e root) ≃g cliqueUnion s Q)
    (hm : 0 < m) (hAvg : s * m ≤ Nat.card (G.neighborSet root)) :
    m.factorial ^ s ≤ Nat.card (pointwiseGraphStabilizer H {e root}) := by
  obtain ⟨part, hAdj⟩ := selected_clique_partition G H e heppa root φ
  simpa only [Fintype.card_fin] using
    factorial_pow_le_root_stabilizer_of_clique_partition G H e heppa root part hAdj hm
      (by simpa only [Fintype.card_fin] using hAvg)

/-- A selected neighbourhood with at least `s+m` vertices in `s`
ambient cliques forces at least `2^m` elements in the root stabilizer. -/
theorem two_pow_le_root_stabilizer_of_local_clique_union
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (root : V) {s Q m : ℕ} (φ : localGraph H (e root) ≃g cliqueUnion s Q)
    (hSize : s + m ≤ Nat.card (G.neighborSet root)) :
    2 ^ m ≤ Nat.card (pointwiseGraphStabilizer H {e root}) := by
  classical
  obtain ⟨part, hAdj⟩ := selected_clique_partition G H e heppa root φ
  have hCount : (∑ i, Nat.card {x // part x = i}) = Nat.card (G.neighborSet root) := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv part)
  have hProd := two_pow_le_clique_factorial_prod Finset.univ
    (fun i => Nat.card {x // part x = i})
    (by simpa only [Finset.card_univ, Fintype.card_fin, hCount] using hSize)
  exact hProd.trans (cluster_product_le_root_stabilizer G H e heppa root part hAdj)

end EPPAIII.Primitive
