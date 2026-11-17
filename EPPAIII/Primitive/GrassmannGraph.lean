import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! # The Grassmann graph on two-dimensional subspaces -/

namespace EPPAIII.Primitive

open Module

/-- The vertices of the Grassmann graph are the two-dimensional subspaces. -/
abbrev GrassmannPlane (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  {P : Submodule F V // finrank F P = 2}

/-- Two planes are joined precisely when their intersection is one-dimensional. -/
def grassmannGraph (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :
    SimpleGraph (GrassmannPlane F V) where
  Adj P Q := finrank F (P.val ⊓ Q.val : Submodule F V) = 1
  symm := by
    constructor
    intro P Q h
    change finrank F (P.val ⊓ Q.val : Submodule F V) = 1 at h
    change finrank F (Q.val ⊓ P.val : Submodule F V) = 1
    rw [inf_comm Q.val P.val]
    exact h
  loopless := by
    constructor
    intro P h
    change finrank F (P.val ⊓ P.val : Submodule F V) = 1 at h
    rw [inf_idem, P.property] at h
    omega

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Distinct two-dimensional subspaces intersect in either one dimension or zero. -/
theorem grassmannGraph_adj_iff_intersection_ne_bot [FiniteDimensional F V]
    {P Q : GrassmannPlane F V} (hPQ : P ≠ Q) :
    (grassmannGraph F V).Adj P Q ↔ (P.val ⊓ Q.val : Submodule F V) ≠ ⊥ := by
  have hlt : (P.val ⊓ Q.val : Submodule F V) < P.val := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    apply hPQ
    apply Subtype.ext
    apply Submodule.eq_of_le_of_finrank_le (show P.val ≤ Q.val by rw [← he]; exact inf_le_right)
    rw [P.property, Q.property]
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  rw [P.property] at hdim
  change finrank F (P.val ⊓ Q.val : Submodule F V) = 1 ↔ _
  have hZero : finrank F (P.val ⊓ Q.val : Submodule F V) = 0 ↔
      (P.val ⊓ Q.val : Submodule F V) = ⊥ := Submodule.finrank_eq_zero
  constructor
  · intro hOne hBot
    have hRank := hZero.mpr hBot
    omega
  · intro hNonzero
    have hRank : finrank F (P.val ⊓ Q.val : Submodule F V) ≠ 0 :=
      fun h => hNonzero (hZero.mp h)
    omega

private theorem card_nonzero_vectors {W : Type*} [Zero W] [Finite W] :
    Nat.card {v : W // v ≠ 0} = Nat.card W - 1 := by
  classical
  let := Fintype.ofFinite W
  let := Fintype.ofFinite {v : W // v ≠ 0}
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private theorem card_finite_vectorSpace {W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] [Fintype F] :
    Nat.card W = Fintype.card F ^ finrank F W := by
  let e : W ≃ₗ[F] (Fin (finrank F W) → F) := LinearEquiv.ofFinrankEq _ _ (by simp)
  rw [Nat.card_congr e.toEquiv]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_pi_const F _

/-- Independent Grassmann vertices have pairwise disjoint nonzero vector sets.
This gives the packing bound used for the second constituent, since any
independent set in an induced subgraph is independent in the host. -/
theorem grassmannGraph_independent_packing [FiniteDimensional F V]
    [Fintype F] [Finite V] {k : ℕ} (f : Fin k ↪ GrassmannPlane F V)
    (hIndependent : ∀ i j, ¬ (grassmannGraph F V).Adj (f i) (f j)) :
    k * (Fintype.card F ^ 2 - 1) ≤ Fintype.card F ^ finrank F V - 1 := by
  classical
  let family (i : Fin k) := {v : (f i).val // v ≠ 0}
  let embed : (Σ i, family i) → {v : V // v ≠ 0} := fun ij =>
    ⟨ij.2.val.val, fun h => ij.2.property (Subtype.ext h)⟩
  have hinj : Function.Injective embed := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    have hxy : x.val.val = y.val.val :=
      congrArg (fun v : {v : V // v ≠ 0} => v.val) h
    have hij : i = j := by
      by_contra hne
      have hbot : ((f i).val ⊓ (f j).val : Submodule F V) = ⊥ := by
        by_contra hNonzero
        exact hIndependent i j ((grassmannGraph_adj_iff_intersection_ne_bot
          (fun hp => hne (f.injective hp))).mpr hNonzero)
      have hx : x.val.val ∈ ((f i).val ⊓ (f j).val : Submodule F V) :=
        ⟨x.val.property, hxy.symm ▸ y.val.property⟩
      have hx0 : x.val.val = 0 := (Submodule.mem_bot F).mp (hbot ▸ hx)
      exact x.property (Subtype.ext hx0)
    subst j
    congr
    exact Subtype.ext (Subtype.ext hxy)
  have hCard := Nat.card_le_card_of_injective embed hinj
  rw [Nat.card_sigma, card_nonzero_vectors (W := V), card_finite_vectorSpace (F := F) (W := V)] at hCard
  have hFamily (i : Fin k) : Nat.card (family i) = Fintype.card F ^ 2 - 1 := by
    dsimp [family]
    rw [card_nonzero_vectors, card_finite_vectorSpace (F := F), (f i).property]
  simpa only [hFamily, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul] using hCard

/-- On distinct neighbours of the root, the lines obtained by intersecting
with the root are distinct throughout any independent set. -/
theorem grassmannGraph_local_independent_bound [FiniteDimensional F V] [Fintype F]
    {k : ℕ} (root : GrassmannPlane F V)
    (f : Fin k ↪ (grassmannGraph F V).neighborSet root)
    (hIndependent : ∀ i j, ¬ (grassmannGraph F V).Adj (f i).val (f j).val) :
    k ≤ Fintype.card F + 1 := by
  classical
  let I (i : Fin k) : Submodule F V := root.val ⊓ (f i).val.val
  let J (i : Fin k) : Submodule F root.val := (I i).comap root.val.subtype
  have hle (i : Fin k) : I i ≤ root.val := inf_le_left
  have hRank (i : Fin k) : finrank F (J i) = 1 :=
    (Submodule.comapSubtypeEquivOfLe (hle i)).finrank_eq.trans (f i).property
  let point (i : Fin k) : Projectivization F root.val := Projectivization.mk'' (J i) (hRank i)
  have hInjective : Function.Injective point := by
    intro i j h
    by_contra hne
    have he : J i = J j := by
      simpa only [point, Projectivization.submodule_mk''] using
        congrArg Projectivization.submodule h
    have hNonzero : J i ≠ ⊥ := by
      intro hz
      have := hRank i
      rw [hz, finrank_bot] at this
      omega
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hNonzero
    have hv' : v ∈ J j := he ▸ hv
    have hV : v.val ∈ ((f i).val.val ⊓ (f j).val.val : Submodule F V) :=
      ⟨(show v.val ∈ I i from hv).2, (show v.val ∈ I j from hv').2⟩
    have hInter : ((f i).val.val ⊓ (f j).val.val : Submodule F V) ≠ ⊥ := by
      intro hbot
      exact hv0 (Subtype.ext ((Submodule.mem_bot F).mp (hbot ▸ hV)))
    have hDistinct : (f i).val ≠ (f j).val := fun h' => hne (f.injective (Subtype.ext h'))
    exact hIndependent i j ((grassmannGraph_adj_iff_intersection_ne_bot hDistinct).mpr hInter)
  letI : Finite V := Module.finite_of_finite F
  have hCard := Nat.card_le_card_of_injective point hInjective
  rwa [Nat.card_fin, Projectivization.card_of_finrank_two F _ root.property,
    Nat.card_eq_fintype_card] at hCard

end EPPAIII.Primitive
