import EPPAIII.Primitive.AffineMatchingExclusion
import Mathlib.Combinatorics.SimpleGraph.Sum

/-! # Local cluster profiles in the order-64 generalized quadrangle -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem card_automorphisms_sum_divisibility {U V : Type*}
    (G : SimpleGraph U) (H : SimpleGraph V) :
    Nat.card (graphAutomorphisms G) * Nat.card (graphAutomorphisms H) ∣
      Nat.card (graphAutomorphisms (G ⊕g H)) := by
  let f : graphAutomorphisms G × graphAutomorphisms H →* graphAutomorphisms (G ⊕g H) :=
    { toFun := fun p => ⟨Equiv.sumCongr p.1.val p.2.val, by
        rintro (u | u) (v | v)
        · exact p.1.property u v
        · rfl
        · rfl
        · exact p.2.property u v⟩
      map_one' := Subtype.ext (Equiv.ext (by rintro (u | u) <;> rfl))
      map_mul' := fun p q => Subtype.ext (Equiv.ext (by rintro (u | u) <;> rfl)) }
  have hInjective : Function.Injective f := by
    intro p q h
    apply Prod.ext <;> apply Subtype.ext <;> apply Equiv.ext
    · intro u
      exact Sum.inl.inj (congrArg (fun g : graphAutomorphisms (G ⊕g H) => g.val (Sum.inl u)) h)
    · intro v
      exact Sum.inr.inj (congrArg (fun g : graphAutomorphisms (G ⊕g H) => g.val (Sum.inr v)) h)
  simpa only [Nat.card_prod] using Subgroup.card_dvd_of_injective f hInjective

private def clusterFibre {s : ℕ} (S : Finset (Fin s × Fin 3)) (i : Fin s) :=
  S.filter (fun w => w.1 = i)

private def clusterRows {s : ℕ} (S : Finset (Fin s × Fin 3)) (t : ℕ) :=
  Finset.univ.filter (fun i => (clusterFibre S i).card = t)

private theorem cluster_fibre_card_le {s : ℕ} (S : Finset (Fin s × Fin 3)) (i : Fin s) :
    (clusterFibre S i).card ≤ 3 := by
  let e : (↑(clusterFibre S i) : Set (Fin s × Fin 3)) ↪ Fin 3 :=
    ⟨fun w => w.val.2, fun w z h => by
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp w.property).2.trans (Finset.mem_filter.mp z.property).2.symm
      · exact h⟩
  simpa using Fintype.card_le_of_embedding e

private theorem cluster_profile_weight {s : ℕ} (S : Finset (Fin s × Fin 3)) :
    S.card = (clusterRows S 1).card + 2 * (clusterRows S 2).card + 3 * (clusterRows S 3).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp only [clusterRows, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_boole]
  change (clusterFibre S i).card = _
  have h := cluster_fibre_card_le S i
  rcases (show (clusterFibre S i).card = 0 ∨ (clusterFibre S i).card = 1 ∨
      (clusterFibre S i).card = 2 ∨ (clusterFibre S i).card = 3 by omega) with
      h0 | h1 | h2 | h3 <;> simp_all

private theorem cluster_profile_length {s : ℕ} (S : Finset (Fin s × Fin 3)) :
    (clusterRows S 1).card + (clusterRows S 2).card + (clusterRows S 3).card ≤ s := by
  classical
  simp only [clusterRows, Finset.card_filter, ← Finset.sum_add_distrib]
  refine le_trans (Finset.sum_le_sum (g := fun _i => (1 : ℕ)) ?_) (by simp)
  intro i hi
  by_cases h1 : (clusterFibre S i).card = 1 <;> by_cases h2 : (clusterFibre S i).card = 2 <;>
    by_cases h3 : (clusterFibre S i).card = 3 <;> simp_all

private structure ClusterChart {s : ℕ} (S : Finset (Fin s × Fin 3)) (m t : ℕ) where
  embedding : cliqueUnion m t ↪g (cliqueUnion s 3).induce (↑S : Set _)
  fibre_card : ∀ x, (clusterFibre S (embedding x).val.1).card = t

set_option maxHeartbeats 1000000 in
private noncomputable def cluster_chart {s m t : ℕ} (S : Finset (Fin s × Fin 3))
    (h : (clusterRows S t).card = m) : ClusterChart S m t := by
  classical
  let i : Fin m ≃ (↑(clusterRows S t) : Set (Fin s)) :=
    (Fintype.equivFinOfCardEq (by simpa using h)).symm
  have hIndex (j : Fin m) : (clusterFibre S (i j).val).card = t :=
    (Finset.mem_filter.mp (i j).property).2
  let coord (j : Fin m) : Fin t ≃ (↑(clusterFibre S (i j).val) : Set (Fin s × Fin 3)) :=
    (Fintype.equivFinOfCardEq (by simpa using hIndex j)).symm
  let f (a : Fin m × Fin t) : (↑S : Set (Fin s × Fin 3)) :=
    ⟨(coord a.1 a.2).val, (Finset.mem_filter.mp (coord a.1 a.2).property).1⟩
  have hf (a : Fin m × Fin t) : (f a).val.1 = (i a.1).val :=
    (Finset.mem_filter.mp (coord a.1 a.2).property).2
  have hFirst (a b : Fin m × Fin t) : (f a).val.1 = (f b).val.1 ↔ a.1 = b.1 := by
    rw [hf a, hf b]
    exact ⟨fun h => i.injective (Subtype.ext h), fun h => congrArg (fun j => (i j).val) h⟩
  have hSecond (j : Fin m) (a b : Fin t) :
      (f (j,a)).val.2 = (f (j,b)).val.2 ↔ a = b := by
    refine ⟨fun h => (coord j).injective (Subtype.ext (Prod.ext
      ((hf (j,a)).trans (hf (j,b)).symm) h)), fun h => congrArg (fun x => (f (j,x)).val.2) h⟩
  refine ⟨⟨⟨f, ?_⟩, ?_⟩, ?_⟩
  · rintro ⟨a,i⟩ ⟨b,j⟩ h
    have hab : a = b := (hFirst (a,i) (b,j)).mp (congrArg (fun w => w.val.1) h)
    subst b
    exact Prod.ext rfl ((hSecond _ _ _).mp (congrArg (fun w => w.val.2) h))
  · rintro ⟨a,i⟩ ⟨b,j⟩
    change ((f (a,i)).val.1 = (f (b,j)).val.1 ∧ (f (a,i)).val.2 ≠ (f (b,j)).val.2) ↔
      a = b ∧ i ≠ j
    rw [hFirst]
    by_cases h : a = b
    · subst b
      simpa using (not_congr (hSecond a i j))
    · simp [h]
  · intro a
    change (clusterFibre S (f a).val.1).card = t
    rw [hf a]
    exact hIndex a.1

private def clusterSectionOrder (m₁ m₂ m₃ : ℕ) :=
  m₁.factorial * 1 ^ m₁ * (m₂.factorial * 2 ^ m₂ * (m₃.factorial * 6 ^ m₃))

private theorem gq_cluster_profile (m₁ m₂ m₃ : ℕ) (hComp : m₁ + m₂ + m₃ ≤ 6)
    (hWeight : m₁ + 2 * m₂ + 3 * m₃ = 9) (hDiv : clusterSectionOrder m₁ m₂ m₃ ∣ 2160) :
    (m₁ = 1 ∧ m₂ = 1 ∧ m₃ = 2) ∨ (m₁ = 3 ∧ m₂ = 0 ∧ m₃ = 2) := by
  have hg : ∀ a b c : Fin 7, a.val + b.val + c.val ≤ 6 →
      a.val + 2 * b.val + 3 * c.val = 9 → clusterSectionOrder a.val b.val c.val ∣ 2160 →
      (a.val = 1 ∧ b.val = 1 ∧ c.val = 2) ∨ (a.val = 3 ∧ b.val = 0 ∧ c.val = 2) := by decide
  exact hg ⟨m₁, by omega⟩ ⟨m₂, by omega⟩ ⟨m₃, by omega⟩ hComp hWeight hDiv

/-- The nonlocal constituent of the collinearity graph of (GQ(3,5))
fails all four forms by its order and degree. -/
theorem affine_gqThreeFive_nonlocal_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 64 18 2 6) (root : V) :
    let G := nonlocalGraph H root
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  exact regular_profile_excludes_all_forms (n := 45) (d := 12)
    (constituentGraph_profile H ⟨64, 18, 2, 6⟩ h root true)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private def separated_sum_embedding {U V W : Type*}
    {G : SimpleGraph U} {H : SimpleGraph V} {K : SimpleGraph W}
    (f : G ↪g K) (g : H ↪g K)
    (hSep : ∀ x y, f x ≠ g y ∧ ¬ K.Adj (f x) (g y)) : G ⊕g H ↪g K := by
  refine ⟨⟨Sum.elim f g, ?_⟩, ?_⟩
  · rintro (x | x) (y | y) h
    · exact congrArg Sum.inl (f.injective h)
    · exact ((hSep x y).1 h).elim
    · exact ((hSep y x).1 h.symm).elim
    · exact congrArg Sum.inr (g.injective h)
  · rintro (x | x) (y | y)
    · exact f.map_rel_iff
    · exact (iff_false_intro (hSep x y).2).trans
        (iff_false_intro (not_adj_sum_inl_inr (G := G) (H := H) x y)).symm
    · exact (iff_false_intro (fun h : K.Adj (g x) (f y) => (hSep y x).2 h.symm)).trans
        (iff_false_intro (fun h => not_adj_sum_inl_inr (G := G) (H := H) y x h.symm)).symm
    · exact g.map_rel_iff

private theorem cluster_charts_separated {s m n t u : ℕ}
    {S : Finset (Fin s × Fin 3)} (f : ClusterChart S m t) (g : ClusterChart S n u)
    (ht : t ≠ u) (x : Fin m × Fin t) (y : Fin n × Fin u) :
    f.embedding x ≠ g.embedding y ∧
      ¬ ((cliqueUnion s 3).induce (↑S : Set _)).Adj (f.embedding x) (g.embedding y) := by
  have hFirst : (f.embedding x).val.1 ≠ (g.embedding y).val.1 := by
    intro h
    exact ht ((f.fibre_card x).symm.trans ((congrArg (fun i => (clusterFibre S i).card) h).trans
      (g.fibre_card y)))
  exact ⟨fun h => hFirst (congrArg (fun v => v.val.1) h), fun h => hFirst h.1⟩

private def cluster_pair_chart {s m n t u : ℕ}
    {S : Finset (Fin s × Fin 3)} (f : ClusterChart S m t) (g : ClusterChart S n u) (ht : t ≠ u) :
    cliqueUnion m t ⊕g cliqueUnion n u ↪g (cliqueUnion s 3).induce (↑S : Set _) :=
  separated_sum_embedding f.embedding g.embedding (cluster_charts_separated f g ht)

private def cluster_triple_chart {s m₁ m₂ m₃ : ℕ}
    {S : Finset (Fin s × Fin 3)} (f₁ : ClusterChart S m₁ 1)
    (f₂ : ClusterChart S m₂ 2) (f₃ : ClusterChart S m₃ 3) :
    cliqueUnion m₁ 1 ⊕g (cliqueUnion m₂ 2 ⊕g cliqueUnion m₃ 3) ↪g
      (cliqueUnion s 3).induce (↑S : Set _) :=
  separated_sum_embedding f₁.embedding (cluster_pair_chart f₂ f₃ (by decide))
    (fun x y => match y with
      | Sum.inl y => cluster_charts_separated f₁ f₂ (by decide) x y
      | Sum.inr y => cluster_charts_separated f₁ f₃ (by decide) x y)

private theorem cluster_section_order_dvd (m₁ m₂ m₃ : ℕ) :
    clusterSectionOrder m₁ m₂ m₃ ∣
      Nat.card (graphAutomorphisms
        (cliqueUnion m₁ 1 ⊕g (cliqueUnion m₂ 2 ⊕g cliqueUnion m₃ 3))) := by
  have h23 := card_automorphisms_sum_divisibility (cliqueUnion m₂ 2) (cliqueUnion m₃ 3)
  have h123 := card_automorphisms_sum_divisibility (cliqueUnion m₁ 1)
    (cliqueUnion m₂ 2 ⊕g cliqueUnion m₃ 3)
  have h := (mul_dvd_mul (dvd_refl (Nat.card (graphAutomorphisms (cliqueUnion m₁ 1)))) h23).trans h123
  rw [card_automorphisms_cliqueUnion (by decide), card_automorphisms_cliqueUnion (by decide),
    card_automorphisms_cliqueUnion (by decide)] at h
  exact h

private def singleton_tail_chart {s m : ℕ} {S : Finset (Fin s × Fin 3)}
    (f : ClusterChart S (m + 1) 1) : ClusterChart S m 1 := by
  let shift : cliqueUnion m 1 ↪g cliqueUnion (m + 1) 1 :=
    ⟨⟨fun x => (x.1.succ, x.2), fun x y h =>
        Prod.ext (Fin.succ_inj.mp (congrArg Prod.fst h))
          (congrArg (fun z : Fin (m + 1) × Fin 1 => z.2) h)⟩,
      fun {_ _} => and_congr Fin.succ_inj Iff.rfl⟩
  exact ⟨f.embedding.comp shift, fun x => f.fibre_card (shift x)⟩

private theorem first_singleton_separated {s m : ℕ} {S : Finset (Fin s × Fin 3)}
    (f : ClusterChart S (m + 1) 1) (x : Fin m × Fin 1) :
    f.embedding (0, 0) ≠ (singleton_tail_chart f).embedding x ∧
      ¬ ((cliqueUnion s 3).induce (↑S : Set _)).Adj (f.embedding (0, 0))
        ((singleton_tail_chart f).embedding x) := by
  change f.embedding (0, 0) ≠ f.embedding (x.1.succ, x.2) ∧
    ¬ ((cliqueUnion s 3).induce (↑S : Set _)).Adj (f.embedding (0, 0))
      (f.embedding (x.1.succ, x.2))
  refine ⟨fun h => Fin.succ_ne_zero x.1 (congrArg Prod.fst (f.embedding.injective h)).symm,
    fun h => ?_⟩
  exact Fin.succ_ne_zero x.1 ((f.embedding.map_rel_iff.mp h).1).symm

private theorem automorphisms_dvd_pair_stabilizer_of_local_embedding {U V W : Type*}
    [Finite V] [Finite W] {J : SimpleGraph U}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (w : G.neighborSet root)
    (f : J ↪g localGraph G root)
    (hSep : ∀ x, w ≠ f x ∧ ¬ (localGraph G root).Adj w (f x)) :
    Nat.card (graphAutomorphisms J) ∣ Nat.card (pointwiseGraphStabilizer H {e root, e w.val}) := by
  classical
  let inclusion : localGraph G root ↪g G :=
    { toEmbedding := Function.Embedding.subtype _
      map_rel_iff' := Iff.rfl }
  let g := inclusion.comp f
  let S := Set.range g
  let U := ({root, w.val} : Finset V)
  have hOutside : ∀ u ∈ U, u ∉ S := by
    intro u hu
    rintro ⟨a, ha⟩
    rcases (show u = root ∨ u = w.val by simpa [U] using hu) with rfl | rfl
    · exact (f a).property.ne ha.symm
    · exact (hSep a).1 (Subtype.ext ha.symm)
  have hConst : ∀ p : graphAutomorphisms (G.induce S), ∀ u ∈ U, ∀ x : S,
      G.Adj u x.val ↔ G.Adj u (p.val x).val := by
    intro p u hu x
    obtain ⟨a, ha⟩ := x.property
    obtain ⟨b, hb⟩ := (p.val x).property
    rcases (show u = root ∨ u = w.val by simpa [U] using hu) with rfl | rfl
    · exact iff_of_true (ha ▸ (f a).property) (hb ▸ (f b).property)
    · exact iff_of_false (ha ▸ (hSep a).2) (hb ▸ (hSep b).2)
  have hSurj := restrictToSelected_surjective G H e heppa S U hOutside hConst
  have hImage : e '' (↑U : Set V) = {e root, e w.val} := by simp [U]
  rw [card_automorphisms_of_iso g.isoInduceRange, ← hImage]
  exact (Subgroup.card_dvd_of_surjective hSurj).trans
    (setwiseGraphStabilizer H (e '' (↑U : Set V))
      (Set.range ((Function.Embedding.subtype (· ∈ S)).trans e))).card_subgroup_dvd_card

private theorem gq_anchored_cluster_section {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (hPair : ∀ w, H.Adj (e root) w →
      Nat.card (pointwiseGraphStabilizer H {e root, w}) = 120)
    {S : Finset (Fin 6 × Fin 3)}
    (back : (cliqueUnion 6 3).induce (↑S : Set _) ↪g localGraph G root)
    {m₁ m₂ m₃ : ℕ} (f₁ : ClusterChart S (m₁ + 1) 1)
    (f₂ : ClusterChart S m₂ 2) (f₃ : ClusterChart S m₃ 3) :
    clusterSectionOrder m₁ m₂ m₃ ∣ 120 := by
  let f := cluster_triple_chart (singleton_tail_chart f₁) f₂ f₃
  let a := f₁.embedding (0, 0)
  let w := back a
  have hSep : ∀ x, a ≠ f x ∧
      ¬ ((cliqueUnion 6 3).induce (↑S : Set _)).Adj a (f x) := by
    rintro (x | (x | x))
    · exact first_singleton_separated f₁ x
    · exact cluster_charts_separated f₁ f₂ (by decide) (0, 0) x
    · exact cluster_charts_separated f₁ f₃ (by decide) (0, 0) x
  have hDiv := automorphisms_dvd_pair_stabilizer_of_local_embedding G H e heppa root w
    (back.comp f) (fun x => ⟨back.injective.ne (hSep x).1,
      fun h => (hSep x).2 (back.map_rel_iff.mp h)⟩)
  rw [hPair (e w.val) ((heppa.1 root w.val).mp w.property)] at hDiv
  exact (cluster_section_order_dvd m₁ m₂ m₃).trans hDiv

/-- A selected local constituent of the collinearity graph of (GQ(3,5))
has at most eight vertices. The only nine-vertex profiles compatible with
the point stabilizer force a section of order 144 after fixing a singleton. -/
theorem affine_gqThreeFive_local_order_le_eight {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (φ : localGraph H (e root) ≃g cliqueUnion 6 3)
    (hPoint : Nat.card (pointwiseGraphStabilizer H {e root}) = 2160)
    (hPair : ∀ w, H.Adj (e root) w →
      Nat.card (pointwiseGraphStabilizer H {e root, w}) = 120) :
    Nat.card (G.neighborSet root) ≤ 8 := by
  classical
  let := Fintype.ofFinite V
  by_contra! hSelected
  let η : localGraph G root ↪g localGraph H (e root) :=
    { toEmbedding := restrictEmbedding e (fun x hx => (heppa.1 root x).mp hx)
      map_rel_iff' := fun {_ _} => (heppa.1 _ _).symm }
  let q := φ.toEmbedding.comp η
  let S : Finset (Fin 6 × Fin 3) := Finset.univ.map q.toEmbedding
  have hS : 9 ≤ S.card := by
    rw [Finset.card_map, Finset.card_univ]
    rw [Nat.card_eq_fintype_card] at hSelected
    omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hS
  have hrange : Set.range q = (↑S : Set _) := by
    ext x
    simp [S]
  let ψ : localGraph G root ≃g (cliqueUnion 6 3).induce (↑S : Set _) :=
    hrange ▸ q.isoInduceRange
  let inclusion : (cliqueUnion 6 3).induce (↑T : Set _) ↪g
      (cliqueUnion 6 3).induce (↑S : Set _) :=
    ⟨⟨fun x => ⟨x.val, hTS x.property⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun z : (↑S : Set (Fin 6 × Fin 3)) => z.val) h)⟩, Iff.rfl⟩
  let back := ψ.symm.toEmbedding.comp inclusion
  let m₁ := (clusterRows T 1).card
  let m₂ := (clusterRows T 2).card
  let m₃ := (clusterRows T 3).card
  let f₁ : ClusterChart T m₁ 1 := cluster_chart T rfl
  let f₂ : ClusterChart T m₂ 2 := cluster_chart T rfl
  let f₃ : ClusterChart T m₃ 3 := cluster_chart T rfl
  have hDiv := automorphisms_dvd_root_stabilizer_of_local_embedding G H e heppa root
    (back.comp (cluster_triple_chart f₁ f₂ f₃))
  rw [hPoint] at hDiv
  have hWeight : m₁ + 2 * m₂ + 3 * m₃ = 9 := (cluster_profile_weight T).symm.trans hT
  rcases gq_cluster_profile m₁ m₂ m₃ (cluster_profile_length T) hWeight
      ((cluster_section_order_dvd m₁ m₂ m₃).trans hDiv) with ⟨h₁,h₂,h₃⟩ | ⟨h₁,h₂,h₃⟩
  · have hf₁ : ClusterChart T (0 + 1) 1 := Eq.mp (congrArg (fun m => ClusterChart T m 1) h₁) f₁
    have hf₂ : ClusterChart T 1 2 := Eq.mp (congrArg (fun m => ClusterChart T m 2) h₂) f₂
    have hf₃ : ClusterChart T 2 3 := Eq.mp (congrArg (fun m => ClusterChart T m 3) h₃) f₃
    exact (by decide : ¬ clusterSectionOrder 0 1 2 ∣ 120)
      (gq_anchored_cluster_section G H e heppa root hPair back hf₁ hf₂ hf₃)
  · have hf₁ : ClusterChart T (2 + 1) 1 := Eq.mp (congrArg (fun m => ClusterChart T m 1) h₁) f₁
    have hf₂ : ClusterChart T 0 2 := Eq.mp (congrArg (fun m => ClusterChart T m 2) h₂) f₂
    have hf₃ : ClusterChart T 2 3 := Eq.mp (congrArg (fun m => ClusterChart T m 3) h₃) f₃
    exact (by decide : ¬ clusterSectionOrder 2 0 2 ∣ 120)
      (gq_anchored_cluster_section G H e heppa root hPair back hf₁ hf₂ hf₃)

/-- The two rooted constituents rule out a half-order EPPA selection in
the collinearity graph of (GQ(3,5)). -/
theorem affine_gqThreeFive_not_eppa {V W : Type*} [Finite V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (hSRG : H.IsSRGWith 64 18 2 6)
    (φ : localGraph H (e root) ≃g cliqueUnion 6 3)
    (hPoint : Nat.card (pointwiseGraphStabilizer H {e root}) = 2160)
    (hPair : ∀ w, H.Adj (e root) w →
      Nat.card (pointwiseGraphStabilizer H {e root, w}) = 120)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hNonlocal :
      Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      let K := nonlocalGraph H (e root)
      (∃ s t, Nonempty (K ≃g cliqueUnion s t) ∨ Nonempty (K ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (K ≃g coverGraph s t X Y) ∨ Nonempty (K ≃g (coverGraph s t X Y)ᶜ))) :
    False := by
  classical
  have hLocalV := affine_gqThreeFive_local_order_le_eight G H e heppa root φ hPoint hPair
  have hLocalW : Nat.card (H.neighborSet (e root)) = 18 :=
    (Nat.card_congr φ.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  have hOrder : Nat.card W = 64 := Nat.card_eq_fintype_card.trans hSRG.card
  have hSplitW := order_eq_one_add_subconstituent_orders H (e root)
  have hSplitV := order_eq_one_add_subconstituent_orders G root
  have hLarge : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} := by omega
  obtain ⟨hC, hCC, hG, hCG⟩ := affine_gqThreeFive_nonlocal_exclude_forms H hSRG (e root)
  rcases hNonlocal hLarge with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
  · rcases h with f | f
    · exact (hC s t).false (Classical.choice f)
    · exact (hCC s t).false (Classical.choice f)
  · rcases h with f | f
    · exact (hG s t X Y).false (Classical.choice f)
    · exact (hCG s t X Y).false (Classical.choice f)

end EPPAIII.Primitive
