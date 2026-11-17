import EPPAIII.Primitive.FactorialStabilizer
import EPPAIII.Primitive.AffineSurvivorExclusions
import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.Subconstituents
import EPPAIII.CliqueCovers.Basic

/-! # Section sizes in the affine matching constituent -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem cliqueUnion_same_block_iff {s t : ℕ} (x y : Fin s × Fin t) :
    x.1 = y.1 ↔ x = y ∨ (cliqueUnion s t).Adj x y := by
  constructor
  · intro h
    by_cases hab : x.2 = y.2
    · exact Or.inl (Prod.ext h hab)
    · exact Or.inr ⟨h, hab⟩
  · rintro (h | h)
    · exact congrArg Prod.fst h
    · exact h.1

private theorem cliqueUnion_aut_same_block {s t : ℕ}
    (p : graphAutomorphisms (cliqueUnion s t)) (x y : Fin s × Fin t) :
    (p.val x).1 = (p.val y).1 ↔ x.1 = y.1 := by
  have hp : IsGraphAutomorphism (cliqueUnion s t) p.val := p.property
  rw [cliqueUnion_same_block_iff, cliqueUnion_same_block_iff]
  exact or_congr p.val.injective.eq_iff (hp x y).symm

/-- The automorphisms are permutations of the nonempty blocks followed by
independent permutations within the blocks. -/
theorem card_automorphisms_cliqueUnion {s t : ℕ} (ht : 0 < t) :
    Nat.card (graphAutomorphisms (cliqueUnion s t)) = s.factorial * t.factorial ^ s := by
  classical
  let a₀ : Fin t := ⟨0, ht⟩
  let E := Equiv.Perm (Fin s) × (Fin s → Equiv.Perm (Fin t))
  let wreath (e : E) : Equiv.Perm (Fin s × Fin t) :=
    { toFun := fun x => (e.1 x.1, e.2 x.1 x.2)
      invFun := fun x => (e.1.symm x.1, (e.2 (e.1.symm x.1)).symm x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  let f (e : E) : graphAutomorphisms (cliqueUnion s t) :=
    ⟨wreath e, by
      intro x y
      change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔
        (e.1 x.1 = e.1 y.1 ∧ e.2 x.1 x.2 ≠ e.2 y.1 y.2)
      constructor
      · rintro ⟨h, hne⟩
        exact ⟨congrArg e.1 h, h ▸ (e.2 x.1).injective.ne hne⟩
      · rintro ⟨h, hne⟩
        have hEq := e.1.injective h
        refine ⟨hEq, fun hab => hne ?_⟩
        simp only [hEq, hab]⟩
  have hInj : Function.Injective f := by
    intro e e' h
    apply Prod.ext
    · apply Equiv.ext
      intro i
      exact congrArg (fun q : graphAutomorphisms (cliqueUnion s t) => (q.val (i, a₀)).1) h
    · funext i
      apply Equiv.ext
      intro a
      exact congrArg (fun q : graphAutomorphisms (cliqueUnion s t) => (q.val (i, a)).2) h
  have hSurj : Function.Surjective f := by
    intro p
    let outer (i : Fin s) := (p.val (i, a₀)).1
    have hOuter : Function.Injective outer := fun i j h =>
      (cliqueUnion_aut_same_block p (i, a₀) (j, a₀)).mp h
    let inner (i : Fin s) (j : Fin t) := (p.val (i, j)).2
    have hInner (i) : Function.Injective (inner i) := by
      intro a b h
      have hSame := (cliqueUnion_aut_same_block p (i, a) (i, b)).mpr rfl
      exact congrArg Prod.snd (p.val.injective (Prod.ext hSame h))
    let σ := Equiv.ofBijective outer (⟨hOuter, Finite.surjective_of_injective hOuter⟩)
    let τ (i : Fin s) := Equiv.ofBijective (inner i) (⟨hInner i, Finite.surjective_of_injective (hInner i)⟩)
    refine ⟨(σ, τ), Subtype.ext (Equiv.ext fun x => Prod.ext ?_ rfl)⟩
    exact (cliqueUnion_aut_same_block p (x.1, a₀) x).mpr rfl
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hInj, hSurj⟩), Nat.card_eq_fintype_card]
  simp [E, Fintype.card_perm]

private theorem large_matching_subset {s : ℕ} (S : Finset (Fin s × Fin 2))
    (hS : 11 ≤ S.card) :
    Nonempty ((⊥ : SimpleGraph (Fin 8)) ↪g (cliqueUnion s 2).induce (↑S : Set _)) ∨
      Nonempty (cliqueUnion 4 2 ↪g (cliqueUnion s 2).induce (↑S : Set _)) := by
  classical
  let I := S.image Prod.fst
  let double (i : Fin s) := (i, 0) ∈ S ∧ (i, 1) ∈ S
  let D := I.filter double
  have hCoord (a : Fin 2) : a = 0 ∨ a = 1 := by
    have ha := a.isLt
    obtain h | h : a.val = 0 ∨ a.val = 1 := by omega
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have hbound : S.card ≤ I.card + D.card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (s := S) (t := I) (fun _ hm => Finset.mem_image_of_mem Prod.fst hm)]
    rw [show I.card = ∑ _i ∈ I, (1 : ℕ) by simp,
      show D.card = ∑ i ∈ I, if double i then 1 else 0 from Finset.card_filter _ _,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases hDouble : double i
    · simp only [hDouble, ite_true]
      have hsub : S.filter (fun w => w.1 = i) ⊆ {(i, 0), (i, 1)} := by
        intro w hw
        obtain ⟨_, hw⟩ := Finset.mem_filter.mp hw
        rcases hCoord w.2 with h | h
        · rw [show w = (i, 0) from Prod.ext hw h]
          simp
        · rw [show w = (i, 1) from Prod.ext hw h]
          simp
      exact (Finset.card_le_card hsub).trans (by simp)
    · simp only [hDouble, ite_false, Nat.add_zero]
      apply Finset.card_le_one.mpr
      intro w hw z hz
      obtain ⟨hw, hiw⟩ := Finset.mem_filter.mp hw
      obtain ⟨hz, hiz⟩ := Finset.mem_filter.mp hz
      rcases hCoord w.2 with hwa | hwa <;> rcases hCoord z.2 with hza | hza
      · exact Prod.ext (hiw.trans hiz.symm) (hwa.trans hza.symm)
      · exact (hDouble ⟨(Prod.ext hiw hwa : w = (i, 0)) ▸ hw,
          (Prod.ext hiz hza : z = (i, 1)) ▸ hz⟩).elim
      · exact (hDouble ⟨(Prod.ext hiz hza : z = (i, 0)) ▸ hz,
          (Prod.ext hiw hwa : w = (i, 1)) ▸ hw⟩).elim
      · exact Prod.ext (hiw.trans hiz.symm) (hwa.trans hza.symm)
  by_cases hI : 8 ≤ I.card
  · obtain ⟨j⟩ : Nonempty (Fin 8 ↪ I) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hI)
    have hPreimage (a : Fin 8) : ∃ w ∈ S, w.1 = (j a).val :=
      Finset.mem_image.mp (j a).property
    let f (a : Fin 8) : (↑S : Set _) :=
      ⟨Classical.choose (hPreimage a), (Classical.choose_spec (hPreimage a)).1⟩
    have hIndex (a : Fin 8) : (f a).val.1 = (j a).val :=
      (Classical.choose_spec (hPreimage a)).2
    have hfIndex (a b : Fin 8) (h : (f a).val.1 = (f b).val.1) : a = b :=
      j.injective (Subtype.ext ((hIndex a).symm.trans (h.trans (hIndex b))))
    refine Or.inl ⟨⟨f, fun a b h => hfIndex a b (congrArg (fun w => w.val.1) h)⟩, ?_⟩
    intro a b
    change ((f a).val.1 = (f b).val.1 ∧ (f a).val.2 ≠ (f b).val.2) ↔ False
    exact ⟨fun h => h.2 (congrArg (fun w => (f w).val.2) (hfIndex a b h.1)), False.elim⟩
  · have hD : 4 ≤ D.card := by omega
    obtain ⟨j⟩ : Nonempty (Fin 4 ↪ D) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hD)
    let f (a : Fin 4 × Fin 2) : (↑S : Set _) := ⟨((j a.1).val, a.2), by
      have hDouble : double (j a.1).val := (Finset.mem_filter.mp (j a.1).property).2
      rcases hCoord a.2 with h | h
      · exact h ▸ hDouble.1
      · exact h ▸ hDouble.2⟩
    have hj (a b : Fin 4) : (j a).val = (j b).val ↔ a = b :=
      ⟨fun h => j.injective (Subtype.ext h), fun h => congrArg (fun i => (j i).val) h⟩
    refine Or.inr ⟨⟨f, fun a b h => Prod.ext
      ((hj _ _).mp (congrArg (fun w => w.val.1) h)) (congrArg (fun w => w.val.2) h)⟩, ?_⟩
    intro a b
    exact and_congr (hj _ _) Iff.rfl

private theorem card_automorphisms_of_iso {U U' : Type*}
    {J : SimpleGraph U} {J' : SimpleGraph U'} (φ : J ≃g J') :
    Nat.card (graphAutomorphisms J) = Nat.card (graphAutomorphisms J') := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv φ.toEquiv.permCongr
  intro p
  change IsGraphAutomorphism J p ↔ IsGraphAutomorphism J' (φ.toEquiv.permCongr p)
  constructor
  · intro hp a b
    change J'.Adj a b ↔ J'.Adj (φ (p (φ.symm a))) (φ (p (φ.symm b)))
    rw [φ.map_rel_iff, ← hp, ← φ.map_rel_iff, φ.apply_symm_apply, φ.apply_symm_apply]
  · intro hp a b
    have h := hp (φ a) (φ b)
    change J'.Adj (φ a) (φ b) ↔
      J'.Adj (φ (p (φ.symm (φ a)))) (φ (p (φ.symm (φ b)))) at h
    rw [φ.symm_apply_apply, φ.symm_apply_apply, φ.map_rel_iff, φ.map_rel_iff] at h
    exact h

private theorem automorphisms_dvd_root_stabilizer_of_local_embedding {U V W : Type*}
    [Finite V] [Finite W] {J : SimpleGraph U}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (f : J ↪g localGraph G root) :
    Nat.card (graphAutomorphisms J) ∣ Nat.card (pointwiseGraphStabilizer H {e root}) := by
  let inclusion : localGraph G root ↪g G :=
    { toEmbedding := Function.Embedding.subtype _
      map_rel_iff' := Iff.rfl }
  let g := inclusion.comp f
  let S := Set.range g
  have hRoot : root ∉ S := by
    rintro ⟨u, h⟩
    exact (f u).property.ne h.symm
  have hAll (x) (hx : x ∈ S) : G.Adj root x := by
    obtain ⟨u, rfl⟩ := hx
    exact (f u).property
  have hSurj := root_restrictToSelected_surjective G H e heppa root S hRoot
    (fun x hx y hy => iff_of_true (hAll x hx) (hAll y hy))
  rw [card_automorphisms_of_iso g.isoInduceRange]
  exact (Subgroup.card_dvd_of_surjective hSurj).trans
    (setwiseGraphStabilizer H {e root}
      (Set.range ((Function.Embedding.subtype (· ∈ S)).trans e))).card_subgroup_dvd_card

private theorem card_automorphisms_empty {U : Type*} [Fintype U] :
    Nat.card (graphAutomorphisms (⊥ : SimpleGraph U)) = (Fintype.card U).factorial := by
  classical
  let f : graphAutomorphisms (⊥ : SimpleGraph U) ≃ Equiv.Perm U :=
    { toFun := Subtype.val
      invFun := fun p => ⟨p, fun _ _ => Iff.rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_perm]

/-- At most ten vertices may be selected in a rooted BLVS matching
constituent. An eleven-vertex matching selection would contain an
independent eight-set or four disjoint edges. -/
theorem affine_blvs_local_order_le_ten {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (φ : localGraph H (e root) ≃g cliqueUnion 11 2)
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) = 7920) :
    Nat.card (G.neighborSet root) ≤ 10 := by
  classical
  let := Fintype.ofFinite V
  by_contra! hSelected
  let η : localGraph G root ↪g localGraph H (e root) :=
    { toEmbedding := restrictEmbedding e (fun x hx => (heppa.1 root x).mp hx)
      map_rel_iff' := fun {_ _} => (heppa.1 _ _).symm }
  let q := φ.toEmbedding.comp η
  let S : Finset (Fin 11 × Fin 2) := Finset.univ.map q.toEmbedding
  have hS : 11 ≤ S.card := by
    rw [Finset.card_map, Finset.card_univ]
    rw [Nat.card_eq_fintype_card] at hSelected
    omega
  have hrange : Set.range q = (↑S : Set _) := by
    ext x
    simp [S]
  let ψ : localGraph G root ≃g (cliqueUnion 11 2).induce (↑S : Set _) :=
    hrange ▸ q.isoInduceRange
  rcases large_matching_subset S hS with hIndep | hEdges
  · obtain ⟨f⟩ := hIndep
    have hDiv := automorphisms_dvd_root_stabilizer_of_local_embedding G H e heppa root
      (ψ.symm.toEmbedding.comp f)
    rw [card_automorphisms_empty, Fintype.card_fin, hStabilizer] at hDiv
    exact (by decide : ¬ (Nat.factorial 8 ∣ 7920)) hDiv
  · obtain ⟨f⟩ := hEdges
    have hDiv := automorphisms_dvd_root_stabilizer_of_local_embedding G H e heppa root
      (ψ.symm.toEmbedding.comp f)
    rw [card_automorphisms_cliqueUnion (by decide), hStabilizer] at hDiv
    exact (by decide : ¬ (Nat.factorial 4 * Nat.factorial 2 ^ 4 ∣ 7920)) hDiv

/-- The local matching bound for BLVS forces a half-order nonlocal
selection, whose four allowed constituent forms fail by the SRG tuple. -/
theorem affine_blvs_not_eppa {V W : Type*} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (hSRG : H.IsSRGWith 243 22 1 2)
    (φ : localGraph H (e root) ≃g cliqueUnion 11 2)
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) = 7920)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hNonlocal :
      Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      let K := nonlocalGraph H (e root)
      (∃ s t, Nonempty (K ≃g cliqueUnion s t) ∨ Nonempty (K ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (K ≃g coverGraph s t X Y) ∨ Nonempty (K ≃g (coverGraph s t X Y)ᶜ))) :
    False := by
  classical
  have hLocalV := affine_blvs_local_order_le_ten G H e heppa root φ hStabilizer
  have hLocalW : Nat.card (H.neighborSet (e root)) = 22 :=
    (Nat.card_congr φ.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  have hOrder : Nat.card W = 243 := Nat.card_eq_fintype_card.trans hSRG.card
  have hSplitW := order_eq_one_add_subconstituent_orders H (e root)
  have hSplitV := order_eq_one_add_subconstituent_orders G root
  have hLarge : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} := by omega
  obtain ⟨hC, hCC, hG, hCG⟩ := affine_243_22_nonlocal_exclude_forms H hSRG (e root)
  rcases hNonlocal hLarge with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
  · rcases h with ⟨f⟩ | ⟨f⟩
    · exact (hC s t).false (Classical.choice f)
    · exact (hCC s t).false (Classical.choice f)
  · rcases h with ⟨f⟩ | ⟨f⟩
    · exact (hG s t X Y).false (Classical.choice f)
    · exact (hCG s t X Y).false (Classical.choice f)

end EPPAIII.Primitive
