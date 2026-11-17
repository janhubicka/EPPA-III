import EPPAIII.Primitive.AffineExceptionalRefinements
import EPPAIII.Primitive.SporadicConstituentExclusions
import EPPAIII.Primitive.Subconstituents

/-! # Further affine rank-three constituent exclusions -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem card_and_degree_of_profile {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n d : ℕ} (h : HasRegularProfile G (n, d)) :
    Fintype.card V = n ∧ G.IsRegularOfDegree d := by
  refine ⟨Nat.card_eq_fintype_card.symm.trans h.1, ?_⟩
  intro x
  rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
  exact h.2 x

private theorem cover_dimensions {s t n : ℕ} (hn : 0 < n)
    (h : Fintype.card (CoverVertex s t) = n) :
    ∃ (_ : Fin s) (_ : Fin t), s * t = n / 2 ∧ t ∣ n / 2 := by
  obtain ⟨⟨_, i, a⟩⟩ := Fintype.card_pos_iff.mp (h.symm ▸ hn)
  have hHalf : s * t = n / 2 := by
    rw [coverVertex_card, Nat.mul_assoc] at h
    omega
  exact ⟨i, a, hHalf, s, by rw [← hHalf, Nat.mul_comm]⟩

private theorem cover_width_of_degree_data {s t m d : ℕ} {X : CrossType} {Y : Bool}
    (i : Fin s) (a : Fin t) (hHalf : s * t = m) (htDvd : t ∣ m)
    (hDeg : t - 1 + coverDiagonalDegree X t + (if Y then (s - 1) * t else 0) = d) :
    ∃ w : Fin (m + 1), w.val = t ∧ 0 < w.val ∧ w.val ∣ m ∧
      d ∈ coverDegreesAtHalfOrder m w.val := by
  have ht : 0 < t := a.isLt.pos
  have htLe : t ≤ m := by
    simpa only [Nat.one_mul, hHalf] using Nat.mul_le_mul_right t i.isLt.pos
  have hOff : (s - 1) * t = m - t := by rw [Nat.sub_mul, Nat.one_mul, hHalf]
  refine ⟨⟨t, by omega⟩, rfl, ht, htDvd, ?_⟩
  simp only [coverDegreesAtHalfOrder, Finset.mem_insert, Finset.mem_singleton]
  cases X <;> cases Y <;> simp [coverDiagonalDegree, hOff] at hDeg <;> omega

private def otherCoverBlocks {s : ℕ} (i : Fin s) : Finset (Fin s) := Finset.univ.erase i

private theorem card_other_cover_blocks {s : ℕ} (i : Fin s) :
    (otherCoverBlocks i).card = s - 1 := by
  rw [otherCoverBlocks, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

private def complement_cover_common_neighbours_embedding
    {V : Type*} (H : SimpleGraph V) {s t : ℕ}
    {X : CrossType} {Y : Bool} (e : (coverGraph s t X Y)ᶜ ↪g H)
    (i : Fin s) (a b : Fin t) :
    (↑(otherCoverBlocks i) × Fin t) ↪ H.commonNeighbors (e (left i a)) (e (left i b)) := by
  have hCross (z : Fin t) (j : otherCoverBlocks i) (c : Fin t) :
      (coverGraph s t X Y)ᶜ.Adj (left i z) (left j.val c) := by
    have hj : i ≠ j.val := (Finset.mem_erase.mp j.property).1.symm
    exact ⟨fun h => hj (congrArg (fun v : CoverVertex s t => v.2.1) h),
      fun h => hj ((left_induced X Y i j.val z c).mp h).1⟩
  refine ⟨fun x => ⟨e (left x.1.val x.2), e.map_rel_iff.mpr (hCross a x.1 x.2),
    e.map_rel_iff.mpr (hCross b x.1 x.2)⟩, ?_⟩
  intro x y he
  have hval : left x.1.val x.2 = left y.1.val y.2 :=
    e.injective (congrArg Subtype.val he)
  exact Prod.ext
    (Subtype.ext (congrArg (fun v : CoverVertex s t => v.2.1) hval))
    (congrArg (fun v : CoverVertex s t => v.2.2) hval)

private theorem strong_complement_common_neighbours
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {s t : ℕ} (hs : 0 < s) (ht : 2 ≤ t) (X : CrossType) (Y : Bool)
    (e : (coverGraph s t X Y)ᶜ ↪g H) :
    ∃ x y : V, x ≠ y ∧ ¬ H.Adj x y ∧
      (s - 1) * t ≤ Fintype.card (H.commonNeighbors x y) := by
  classical
  let i : Fin s := ⟨0, hs⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hadj : (coverGraph s t X Y).Adj (left i a) (left i b) :=
    (left_induced X Y i i a b).mpr ⟨rfl, hab⟩
  refine ⟨e (left i a), e (left i b), e.injective.ne hadj.ne,
    fun h => (e.map_rel_iff.mp h).2 hadj, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_coe, card_other_cover_blocks,
    Fintype.card_fin] using
    Fintype.card_le_of_embedding (complement_cover_common_neighbours_embedding H e i a b)

private theorem exclude_forms_of_complement_codegree {V W : Type*} [Fintype V] [Fintype W]
    {H : SimpleGraph V} [DecidableRel H.Adj] {G : SimpleGraph W} [DecidableRel G.Adj]
    (inclusion : G ↪g H) {n d m t₀ μ : ℕ} (hProfile : HasRegularProfile G (n, d))
    (hn : 0 < n) (hd : d < n) (hm : n / 2 = m)
    (hUnion : ¬ (d + 1) ∣ n) (hUnionCompl : ¬ (n - d) ∣ n)
    (hCover : ¬ CoverDegreeDivisibility n d)
    (hWidth : ∀ w : Fin (m + 1), 0 < w.val → w.val ∣ m →
      n - 1 - d ∈ coverDegreesAtHalfOrder m w.val → w.val = t₀)
    (ht₀ : 2 ≤ t₀)
    (hμ : ∀ x y : V, x ≠ y → ¬ H.Adj x y → Fintype.card (H.commonNeighbors x y) = μ)
    (hRoot : (μ < m - t₀) ∨
      ∃ r : V, (∀ x : W, H.Adj r (inclusion x)) ∧ μ < m - t₀ + 1) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  obtain ⟨hCard, hReg⟩ := card_and_degree_of_profile hProfile
  obtain ⟨hClique, hComplClique⟩ :=
    regular_profile_excludes_cliqueUnion G hn hd hCard hReg hUnion hUnionCompl
  refine ⟨hClique, hComplClique, ?_, ?_⟩
  · intro s t X Y
    exact ⟨fun φ => hCover (coverDegree_divisibility (coverDegreeCompatible_of_iso hn hCard hReg φ))⟩
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have hSize := φ.card_eq.symm.trans hCard
    obtain ⟨i, a, hHalf, htDvd⟩ := cover_dimensions hn hSize
    rw [hm] at hHalf htDvd
    have hDeg := φ.symm.degree_eq (left i a)
    rw [hReg, degree_compl, hSize, coverGraph_left_degree X Y i a] at hDeg
    have hDegree : t - 1 + coverDiagonalDegree X t + (if Y then (s - 1) * t else 0) =
        n - 1 - d := by
      have hb := (coverGraph s t X Y).degree_lt_card_verts (left i a)
      rw [hSize, coverGraph_left_degree X Y i a] at hb
      omega
    obtain ⟨w, hw, hwPos, hwDiv, hwDeg⟩ := cover_width_of_degree_data i a hHalf htDvd hDegree
    have htEq : t = t₀ := hw.symm.trans (hWidth w hwPos hwDiv hwDeg)
    have ht : 2 ≤ t := htEq ▸ ht₀
    have hoff : (s - 1) * t = m - t₀ := by rw [Nat.sub_mul, Nat.one_mul, hHalf, htEq]
    let e := inclusion.comp φ.symm.toEmbedding
    rcases hRoot with hb | ⟨r, hr, hb⟩
    · obtain ⟨x, y, hxy, hnxy, hbound⟩ :=
        strong_complement_common_neighbours H i.isLt.pos ht X Y e
      rw [hμ x y hxy hnxy, hoff] at hbound
      omega
    · obtain ⟨x, y, hxy, hnxy, hbound⟩ :=
        complement_cover_common_neighbors_with_root H i.isLt.pos ht X Y e r
          (fun z => hr (φ.symm z))
      rw [hμ x y hxy hnxy, hoff] at hbound
      omega

private def induced_inclusion {V : Type*} (H : SimpleGraph V) (S : Set V) :
    H.induce S ↪g H where
  toEmbedding := Function.Embedding.subtype _
  map_rel_iff' := Iff.rfl

/-- The two constituents of the order-81 extraspecial row fail all four forms.
In the local case the root supplies the strict codegree inequality. -/
theorem affine_81_32_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 81 32 13 12)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact exclude_forms_of_complement_codegree (induced_inclusion H (H.neighborSet root))
      (m := 16) (t₀ := 4) (μ := 12)
      (constituentGraph_profile H ⟨81, 32, 13, 12⟩ h root false)
      (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (Or.inr ⟨root, fun x => x.property, by decide⟩)
  · exact exclude_forms_of_complement_codegree
      (induced_inclusion H {x | root ≠ x ∧ ¬ H.Adj root x})
      (m := 24) (t₀ := 4) (μ := 12)
      (constituentGraph_profile H ⟨81, 32, 13, 12⟩ h root true)
      (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (Or.inl (by decide))

/-- The two constituents of the order-169 extraspecial row fail all four forms.
In the local case the root supplies the strict codegree inequality. -/
theorem affine_169_72_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 169 72 31 30)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact exclude_forms_of_complement_codegree (induced_inclusion H (H.neighborSet root))
      (m := 36) (t₀ := 6) (μ := 30)
      (constituentGraph_profile H ⟨169, 72, 31, 30⟩ h root false)
      (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (Or.inr ⟨root, fun x => x.property, by decide⟩)
  · exact exclude_forms_of_complement_codegree
      (induced_inclusion H {x | root ≠ x ∧ ¬ H.Adj root x})
      (m := 48) (t₀ := 6) (μ := 30)
      (constituentGraph_profile H ⟨169, 72, 31, 30⟩ h root true)
      (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (Or.inl (by decide))

private theorem cover_has_block_clique {s t : ℕ} (i : Fin s) (X : CrossType) (Y : Bool) :
    ∃ f : Fin t ↪ CoverVertex s t,
      ∀ a b, a ≠ b → (coverGraph s t X Y).Adj (f a) (f b) := by
  let f : Fin t ↪ CoverVertex s t :=
    ⟨left i, fun _ _ h => congrArg (fun x : CoverVertex s t => x.2.2) h⟩
  exact ⟨f, fun a b hab => (left_induced X Y i i a b).mpr ⟨rfl, hab⟩⟩

private theorem cover_full_has_double_clique {s t : ℕ} (i : Fin s) (Y : Bool) :
    ∃ f : Fin (t + t) ↪ CoverVertex s t,
      ∀ a b, a ≠ b → (coverGraph s t .full Y).Adj (f a) (f b) := by
  let g : Fin t ⊕ Fin t ↪ CoverVertex s t :=
    ⟨Sum.elim (left i) (right i), by
      intro a b h
      cases a <;> cases b
      · exact congrArg Sum.inl (congrArg (fun v : CoverVertex s t => v.2.2) h)
      · exact Bool.noConfusion (congrArg (fun v : CoverVertex s t => v.1) h)
      · exact Bool.noConfusion (congrArg (fun v : CoverVertex s t => v.1) h)
      · exact congrArg Sum.inr (congrArg (fun v : CoverVertex s t => v.2.2) h)⟩
  have hg : ∀ a b, a ≠ b → (coverGraph s t .full Y).Adj (g a) (g b) := by
    rintro (u | u) (v | v) hab
    · exact (left_induced .full Y i i u v).mpr ⟨rfl, fun h => hab (congrArg Sum.inl h)⟩
    · exact full_diag_hits_every_right Y (fun _ => u) i v
    · exact (full_diag_hits_every_right Y (fun _ => v) i u).symm
    · exact (right_induced .full Y i i u v).mpr ⟨rfl, fun h => hab (congrArg Sum.inr h)⟩
  let θ : Fin (t + t) ≃ Fin t ⊕ Fin t := finSumFinEquiv.symm
  exact ⟨θ.toEmbedding.trans g, fun a b hab => hg (θ a) (θ b) (θ.injective.ne hab)⟩

private theorem clique_for_small_odd_cover_degree {s t m d : ℕ}
    {X : CrossType} {Y : Bool} (i : Fin s) (a : Fin t)
    (hHalf : s * t = m) (htDvd : t ∣ m) (hSmall : d < m - 1)
    (hOdd : d % 2 = 1) (hNoMatching : ¬ d ∣ m)
    (hDeg : t - 1 + coverDiagonalDegree X t + (if Y then (s - 1) * t else 0) = d) :
    ∃ f : Fin (d + 1) ↪ CoverVertex s t,
      ∀ a b, a ≠ b → (coverGraph s t X Y).Adj (f a) (f b) := by
  have ht : 0 < t := a.isLt.pos
  have htLe : t ≤ m := by
    simpa only [Nat.one_mul, hHalf] using Nat.mul_le_mul_right t i.isLt.pos
  have hOff : (s - 1) * t = m - t := by rw [Nat.sub_mul, Nat.one_mul, hHalf]
  have hCases : t = d + 1 ∨ X = .full ∧ t + t = d + 1 := by
    cases X <;> cases Y <;> simp [coverDiagonalDegree, hOff] at hDeg ⊢ <;>
      first
      | omega
      | exact (hNoMatching (by rwa [show t = d by omega] at htDvd)).elim
  rcases hCases with h | ⟨rfl, h⟩
  · rw [← h]
    exact cover_has_block_clique i X Y
  · rw [← h]
    exact cover_full_has_double_clique i Y

private def complement_of_iso_to_complement {V W : Type*}
    {G : SimpleGraph V} {M : SimpleGraph W} (φ : G ≃g Mᶜ) : Gᶜ ≃g M where
  toEquiv := φ.toEquiv
  map_rel_iff' := by
    intro a b
    change M.Adj (φ a) (φ b) ↔ a ≠ b ∧ ¬ G.Adj a b
    constructor
    · intro h
      exact ⟨fun he => h.ne (congrArg φ he), fun hadj => (φ.map_rel_iff.mpr hadj).2 h⟩
    · rintro ⟨hne, hn⟩
      exact Classical.byContradiction fun h => hn (φ.map_rel_iff.mp ⟨φ.injective.ne hne, h⟩)

private theorem exclude_forms_of_small_odd_degree_no_clique
    {V W : Type*} [Fintype V] [Fintype W] {H : SimpleGraph V} {G : SimpleGraph W}
    [DecidableRel G.Adj] (inclusion : G ↪g H)
    {n d : ℕ} (hProfile : HasRegularProfile G (n, d)) (hn : 0 < n)
    (hSmall : d < n / 2 - 1) (hOdd : d % 2 = 1) (hNoMatching : ¬ d ∣ n / 2)
    (hUnionCompl : ¬ (n - d) ∣ n)
    (hCoverCompl : ¬ CoverDegreeDivisibility n (n - 1 - d))
    (hNoClique : ∀ f : Fin (d + 1) ↪ V, (∀ i j, i ≠ j → H.Adj (f i) (f j)) → False) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  obtain ⟨hCard, hReg⟩ := card_and_degree_of_profile hProfile
  have hRegCompl : Gᶜ.IsRegularOfDegree (n - 1 - d) := by simpa [hCard] using hReg.compl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    refine ⟨fun φ => ?_⟩
    have hSize : Fintype.card (Fin s × Fin t) = n := φ.card_eq.symm.trans hCard
    obtain ⟨⟨i, a⟩⟩ := Fintype.card_pos_iff.mp (hSize.symm ▸ hn)
    have hDeg := φ.symm.degree_eq (i, a)
    rw [hReg, CliqueCovers.cliqueUnion_degree i.isLt.pos] at hDeg
    have ht : 0 < t := a.isLt.pos
    have htEq : d + 1 = t := by omega
    let f : Fin t ↪ Fin s × Fin t := ⟨fun b => (i, b), fun _ _ h => congrArg Prod.snd h⟩
    let e := (finCongr htEq).toEmbedding.trans f
    exact hNoClique (e.trans (φ.symm.toEmbedding.toEmbedding.trans inclusion.toEmbedding))
      (fun x y hxy => inclusion.map_rel_iff.mpr
        (φ.symm.map_rel_iff.mpr ⟨rfl, (finCongr htEq).injective.ne hxy⟩))
  · intro s t
    refine ⟨fun φ => ?_⟩
    have ψ : Gᶜ ≃g cliqueUnion s t := complement_of_iso_to_complement φ
    have hDiv := cliqueUnion_degree_dvd_order_of_iso hn hCard hRegCompl ψ
    exact hUnionCompl (by simpa only [show n - 1 - d + 1 = n - d by omega] using hDiv)
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have hSize := φ.card_eq.symm.trans hCard
    obtain ⟨i, a, hHalf, htDvd⟩ := cover_dimensions hn hSize
    have hDeg := φ.symm.degree_eq (left i a)
    rw [hReg, coverGraph_left_degree X Y i a] at hDeg
    obtain ⟨f, hf⟩ := clique_for_small_odd_cover_degree i a hHalf htDvd hSmall hOdd hNoMatching
      hDeg.symm
    exact hNoClique (f.trans (φ.symm.toEmbedding.toEmbedding.trans inclusion.toEmbedding))
      (fun x y hxy => inclusion.map_rel_iff.mpr (φ.symm.map_rel_iff.mpr (hf x y hxy)))
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have ψ : Gᶜ ≃g coverGraph s t X Y := complement_of_iso_to_complement φ
    exact hCoverCompl (coverDegree_divisibility (coverDegreeCompatible_of_iso hn hCard hRegCompl ψ))

/-- The degree-240 affine graph on 2401 vertices has no constituent of the four forms.
In the local constituent each remaining model would contain a 60-clique. -/
theorem affine_2401_240_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 2401 240 59 20)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact exclude_forms_of_small_odd_degree_no_clique (induced_inclusion H (H.neighborSet root))
      (constituentGraph_profile H ⟨2401, 240, 59, 20⟩ h root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (affine_2401_240_no_sixty_clique H h)
  · refine regular_profile_excludes_all_forms (n := 2160) (d := 220)
      (constituentGraph_profile H ⟨2401, 240, 59, 20⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 2160 220) (coverDegree_divisibility hc)
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 2160 1939) (coverDegree_divisibility hc)

/-- The degree-480 affine graph on 2401 vertices has no constituent of the four forms.
In the local constituent each remaining model would contain a 120-clique. -/
theorem affine_2401_480_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 2401 480 119 90)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact exclude_forms_of_small_odd_degree_no_clique (induced_inclusion H (H.neighborSet root))
      (constituentGraph_profile H ⟨2401, 480, 119, 90⟩ h root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (affine_2401_480_no_hundred_twenty_clique H h)
  · refine regular_profile_excludes_all_forms (n := 1920) (d := 390)
      (constituentGraph_profile H ⟨2401, 480, 119, 90⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 1920 390) (coverDegree_divisibility hc)
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 1920 1529) (coverDegree_divisibility hc)

private theorem cover_coMatching_nonedge_codegree
    {V : Type*} [Fintype V] {H : SimpleGraph V} [DecidableRel H.Adj]
    {s t : ℕ} (i : Fin s) (a : Fin t) (Y : Bool)
    (e : coverGraph s t .coMatching Y ↪g H) :
    ∃ x y : V, x ≠ y ∧ ¬ H.Adj x y ∧
      2 * (t - 1) ≤ Fintype.card (H.commonNeighbors x y) := by
  classical
  let x := e (left i a)
  let y := e (right i a)
  have hne : x ≠ y := fun h =>
    Bool.noConfusion (congrArg (fun v : CoverVertex s t => v.1) (e.injective h))
  have hno : ¬ H.Adj x y := fun h =>
    ((cross_diag_iff .coMatching Y i a a).mp (e.map_rel_iff.mp h)) rfl
  let J := (Finset.univ : Finset (Fin t)).erase a
  have hCard : Fintype.card J = t - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
  let f (z : Bool × J) : CoverVertex s t := (z.1, i, z.2.val)
  have hf (z : Bool × J) :
      (coverGraph s t .coMatching Y).Adj (left i a) (f z) ∧
      (coverGraph s t .coMatching Y).Adj (right i a) (f z) := by
    rcases z with ⟨b, z⟩
    have hz := (Finset.mem_erase.mp z.property).1
    cases b
    · exact ⟨(left_induced .coMatching Y i i a z.val).mpr ⟨rfl, hz.symm⟩,
        ((cross_diag_iff .coMatching Y i z.val a).mpr hz).symm⟩
    · exact ⟨(cross_diag_iff .coMatching Y i a z.val).mpr hz.symm,
        (right_induced .coMatching Y i i a z.val).mpr ⟨rfl, hz.symm⟩⟩
  let g (z : Bool × J) : H.commonNeighbors x y :=
    ⟨e (f z), e.map_rel_iff.mpr (hf z).1, e.map_rel_iff.mpr (hf z).2⟩
  have hg : Function.Injective g := by
    intro u v huv
    have h := e.injective (congrArg Subtype.val huv)
    exact Prod.ext (congrArg (fun w : CoverVertex s t => w.1) h)
      (Subtype.ext (congrArg (fun w : CoverVertex s t => w.2.2) h))
  refine ⟨x, y, hne, hno, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_bool, hCard] using
    Fintype.card_le_of_injective g hg

private theorem exclude_forms_of_small_even_degree_codegree
    {V W : Type*} [Fintype V] [Fintype W] {H : SimpleGraph V} [DecidableRel H.Adj]
    {G : SimpleGraph W} [DecidableRel G.Adj] (inclusion : G ↪g H)
    {n d μ : ℕ} (hProfile : HasRegularProfile G (n, d)) (hn : 0 < n)
    (hSmall : d < n / 2 - 1) (hEven : d % 2 = 0) (hNoMatching : ¬ d ∣ n / 2)
    (hUnion : ¬ (d + 1) ∣ n) (hUnionCompl : ¬ (n - d) ∣ n)
    (hCoverCompl : ¬ CoverDegreeDivisibility n (n - 1 - d))
    (hμ : ∀ x y : V, x ≠ y → ¬ H.Adj x y → Fintype.card (H.commonNeighbors x y) = μ)
    (hCodegree : μ < d) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  obtain ⟨hCard, hReg⟩ := card_and_degree_of_profile hProfile
  have hd : d < n := by omega
  obtain ⟨hClique, hComplClique⟩ :=
    regular_profile_excludes_cliqueUnion G hn hd hCard hReg hUnion hUnionCompl
  have hRegCompl : Gᶜ.IsRegularOfDegree (n - 1 - d) := by simpa [hCard] using hReg.compl
  refine ⟨hClique, hComplClique, ?_, ?_⟩
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    have hSize := φ.card_eq.symm.trans hCard
    obtain ⟨i, a, hHalf, htDvd⟩ := cover_dimensions hn hSize
    have hDeg := φ.symm.degree_eq (left i a)
    rw [hReg, coverGraph_left_degree X Y i a] at hDeg
    have ht : 0 < t := a.isLt.pos
    have htLe : t ≤ n / 2 := by
      simpa only [Nat.one_mul, hHalf] using Nat.mul_le_mul_right t i.isLt.pos
    have hOff : (s - 1) * t = n / 2 - t := by rw [Nat.sub_mul, Nat.one_mul, hHalf]
    have hType : X = .coMatching ∧ 2 * (t - 1) = d := by
      cases X <;> cases Y <;> simp [coverDiagonalDegree, hOff] at hDeg ⊢ <;>
        first
        | omega
        | exact (hNoMatching (by rwa [show t = d by omega] at htDvd)).elim
        | exact (hUnion (by
            use 2 * s
            rw [← show t = d + 1 by omega]
            rw [coverVertex_card] at hSize
            nlinarith)).elim
    obtain ⟨rfl, hWidth⟩ := hType
    obtain ⟨x, y, hxy, hnxy, hb⟩ :=
      cover_coMatching_nonedge_codegree i a Y (inclusion.comp φ.symm.toEmbedding)
    rw [hWidth, hμ x y hxy hnxy] at hb
    omega
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    exact hCoverCompl (coverDegree_divisibility
      (coverDegreeCompatible_of_iso hn hCard hRegCompl (complement_of_iso_to_complement φ)))

/-- The degree-276 affine graph on 2048 vertices has no constituent of the
four forms. The only numerically possible local cover would have a nonedge
with 44 common neighbours in a host of nonedge codegree 36. -/
theorem affine_2048_276_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 2048 276 44 36)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · exact exclude_forms_of_small_even_degree_codegree
      (induced_inclusion H (H.neighborSet root)) (μ := 36)
      (constituentGraph_profile H ⟨2048, 276, 44, 36⟩ h root false)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (by decide)
  · refine regular_profile_excludes_all_forms (n := 1771) (d := 240)
      (constituentGraph_profile H ⟨2048, 276, 44, 36⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) ?_ ?_
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 1771 240)
        (coverDegree_divisibility hc)
    · exact fun hc => (by decide : ¬ CoverDegreeDivisibility 1771 1530)
        (coverDegree_divisibility hc)

/-- The nonlocal constituent of the Berlekamp–Van Lint–Seidel graph fails
all four forms using only the SRG parameters. -/
theorem affine_243_22_nonlocal_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 243 22 1 2) (root : V) :
    let G := nonlocalGraph H root
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  exact exclude_forms_of_small_even_degree_codegree
      (induced_inclusion H {x | root ≠ x ∧ ¬ H.Adj root x}) (μ := 2)
      (constituentGraph_profile H ⟨243, 22, 1, 2⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun _ _ hxy hna => h.of_not_adj hxy hna) (by decide)

private theorem common_neighbours_with_outside
    {V : Type*} [Fintype V] {H : SimpleGraph V} [DecidableRel H.Adj]
    {s t : ℕ} {X : CrossType} {Y : Bool} (e : (coverGraph s t X Y)ᶜ ↪g H)
    (i : Fin s) (a b : Fin t) {root z : V} (hRoot : ∀ u, H.Adj root (e u))
    (hzRoot : z ≠ root) (hzOut : ¬ H.Adj root z)
    (ha : H.Adj (e (left i a)) z) (hb : H.Adj (e (left i b)) z) :
    (s - 1) * t + 2 ≤ Fintype.card (H.commonNeighbors (e (left i a)) (e (left i b))) := by
  let others := complement_cover_common_neighbours_embedding H e i a b
  let extra (q : Bool) : H.commonNeighbors (e (left i a)) (e (left i b)) :=
    if q then ⟨z, ha, hb⟩ else ⟨root, (hRoot _).symm, (hRoot _).symm⟩
  let f := Sum.elim extra others
  have hinj : Function.Injective f := by
    intro q r hqr
    rcases q with q | q <;> rcases r with r | r
    · apply congrArg Sum.inl
      cases q <;> cases r
      · rfl
      · exact (hzRoot (congrArg Subtype.val hqr).symm).elim
      · exact (hzRoot (congrArg Subtype.val hqr)).elim
      · rfl
    · cases q
      · have h : root = e (left r.1.val r.2) := congrArg Subtype.val hqr
        exact ((hRoot _).ne h).elim
      · have h : z = e (left r.1.val r.2) := congrArg Subtype.val hqr
        exact (hzOut (h ▸ hRoot _)).elim
    · cases r
      · have h : e (left q.1.val q.2) = root := congrArg Subtype.val hqr
        exact ((hRoot _).ne h.symm).elim
      · have h : e (left q.1.val q.2) = z := congrArg Subtype.val hqr
        exact (hzOut (h ▸ hRoot _)).elim
    · exact congrArg Sum.inr (others.injective hqr)
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, card_other_cover_blocks,
    Fintype.card_fin, Fintype.card_bool, Nat.add_comm] using
    Fintype.card_le_of_injective f hinj

private theorem affine_256_no_width_five
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : H.IsSRGWith 256 120 56 56) {s : ℕ} (i : Fin s) (hHalf : s * 5 = 60)
    {X : CrossType} {Y : Bool}
    (e : (coverGraph s 5 X Y)ᶜ ↪g H) (root : V) (hRoot : ∀ u, H.Adj root (e u)) :
    False := by
  classical
  let v (a : Fin 5) := e (left i a)
  let R := H.neighborFinset root
  let T := insert root R
  let A (a : Fin 5) := H.neighborFinset (v a) \ T
  have hR : R.card = 120 := by rw [H.card_neighborFinset_eq_degree, h.regular]
  have hNotRoot : root ∉ R := by simp [R]
  have hT : T.card = 121 := by
    rw [Finset.card_insert_of_notMem hNotRoot, hR]
  have hACard (a : Fin 5) : (A a).card = 63 := by
    have hInter : (H.neighborFinset (v a) ∩ R).card = 56 := by
      have hMem (z : V) : z ∈ H.neighborFinset (v a) ∩ R ↔
          z ∈ H.commonNeighbors root (v a) := by
        simp [R, H.mem_commonNeighbors, and_comm]
      rw [← Fintype.card_of_subtype _ hMem]
      exact h.of_adj root (v a) (hRoot _)
    have hInsert : H.neighborFinset (v a) ∩ T = insert root (H.neighborFinset (v a) ∩ R) := by
      ext z
      by_cases hz : z = root
      · subst z
        simp [v, T, (hRoot (left i a)).symm]
      · simp [T, hz]
    have hSize := Finset.card_sdiff_add_card_inter (H.neighborFinset (v a)) T
    rw [hInsert, Finset.card_insert_of_notMem (fun hr => hNotRoot (Finset.mem_inter.mp hr).2),
      hInter, H.card_neighborFinset_eq_degree, h.regular] at hSize
    exact Nat.eq_sub_of_add_eq hSize
  have hOff : (s - 1) * 5 = 55 := by
    rw [Nat.sub_mul, Nat.one_mul, hHalf]
  have hDisjoint : ((↑(Finset.univ : Finset (Fin 5))) : Set (Fin 5)).PairwiseDisjoint A := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    obtain ⟨ha, hzT⟩ := Finset.mem_sdiff.mp hza
    have hb := (Finset.mem_sdiff.mp hzb).1
    have hzRoot : z ≠ root := fun hz => hzT (Finset.mem_insert.mpr (Or.inl hz))
    have hzOut : ¬ H.Adj root z := fun hz =>
      hzT (Finset.mem_insert_of_mem ((H.mem_neighborFinset root z).mpr hz))
    have hCodegree := common_neighbours_with_outside e i a b hRoot hzRoot hzOut
      ((H.mem_neighborFinset (v a) z).mp ha) ((H.mem_neighborFinset (v b) z).mp hb)
    have hadj : (coverGraph s 5 X Y).Adj (left i a) (left i b) :=
      (left_induced X Y i i a b).mpr ⟨rfl, hab⟩
    have hne := e.injective.ne hadj.ne
    have hNon : ¬ H.Adj (v a) (v b) := fun hAdj => (e.map_rel_iff.mp hAdj).2 hadj
    rw [h.of_not_adj hne hNon, hOff] at hCodegree
    omega
  have hMany : ((Finset.univ : Finset (Fin 5)).biUnion A).card = 315 := by
    rw [Finset.card_biUnion hDisjoint]
    simp [hACard]
  have hSubset : (Finset.univ : Finset (Fin 5)).biUnion A ⊆ Finset.univ \ T := by
    intro z hz
    obtain ⟨a, _, hza⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hza).2⟩
  have hFew : ((Finset.univ : Finset V) \ T).card = 135 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hT, h.card]
  have hbound := Finset.card_le_card hSubset
  rw [hMany, hFew] at hbound
  omega

private theorem affine_256_no_complemented_cover
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (h : H.IsSRGWith 256 120 56 56) (root : V)
    {s t : ℕ} {X : CrossType} {Y : Bool}
    (φ : localGraph H root ≃g (coverGraph s t X Y)ᶜ) : False := by
  classical
  have hp := constituentGraph_profile H ⟨256, 120, 56, 56⟩ h root false
  have hCard : Fintype.card (H.neighborSet root) = 120 :=
    Nat.card_eq_fintype_card.symm.trans hp.1
  have hReg : (localGraph H root).IsRegularOfDegree 56 := by
    intro x
    rw [← (localGraph H root).card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.2 x
  have hSize := φ.card_eq.symm.trans hCard
  obtain ⟨i, a, hn, htDvd⟩ := cover_dimensions (by decide) hSize
  have hHalf : s * t = 60 := hn
  have hDeg := φ.symm.degree_eq (left i a)
  rw [hReg, degree_compl, hSize, coverGraph_left_degree X Y i a] at hDeg
  have hDegree : t - 1 + coverDiagonalDegree X t + (if Y then (s - 1) * t else 0) =
      63 := by
    have hb := (coverGraph s t X Y).degree_lt_card_verts (left i a)
    rw [hSize, coverGraph_left_degree X Y i a] at hb
    omega
  obtain ⟨w, hw, hPos, hDvd, hwDeg⟩ := cover_width_of_degree_data i a hHalf htDvd hDegree
  have hWidth : ∀ w : Fin 61, 0 < w.val → w.val ∣ 60 →
      63 ∈ coverDegreesAtHalfOrder 60 w.val → w.val = 4 ∨ w.val = 5 := by decide
  rcases hWidth w hPos hDvd hwDeg with ht | ht
  · have htEq : t = 4 := hw.symm.trans ht
    let e := (induced_inclusion H (H.neighborSet root)).comp φ.symm.toEmbedding
    obtain ⟨x, y, hxy, hNon, hb⟩ := complement_cover_common_neighbors_with_root H
      i.isLt.pos (by omega) X Y e root (fun z => (φ.symm z).property)
    have hOff : (s - 1) * t = 56 := by rw [Nat.sub_mul, Nat.one_mul, hHalf, htEq]
    rw [h.of_not_adj hxy hNon, hOff] at hb
    omega
  · have htEq : t = 5 := hw.symm.trans ht
    clear hw
    subst t
    let e := (induced_inclusion H (H.neighborSet root)).comp φ.symm.toEmbedding
    exact affine_256_no_width_five H h i hHalf e root (fun z => (φ.symm z).property)

/-- The degree-120 affine graph on 256 vertices has neither constituent
of the four forms. At width five, same-side common neighbours and the
root saturate the ambient nonedge codegree. -/
theorem affine_256_120_constituents_exclude_forms {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 256 120 56 56)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  cases side
  · let G := localGraph H root
    have hp := constituentGraph_profile H ⟨256, 120, 56, 56⟩ h root false
    have hCard : Fintype.card (H.neighborSet root) = 120 :=
      Nat.card_eq_fintype_card.symm.trans hp.1
    have hReg : G.IsRegularOfDegree 56 := by
      intro x
      rw [← G.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
      exact hp.2 x
    obtain ⟨hClique, hCoClique⟩ := regular_profile_excludes_cliqueUnion G
      (by decide) (by decide) hCard hReg (by decide) (by decide)
    refine ⟨hClique, hCoClique, ?_, fun _ _ _ _ => ⟨affine_256_no_complemented_cover H h root⟩⟩
    intro s t X Y
    exact ⟨fun φ => (by decide : ¬ CoverDegreeDivisibility 120 56)
      (coverDegree_divisibility (coverDegreeCompatible_of_iso (by decide) hCard hReg φ))⟩
  · exact regular_profile_excludes_all_forms (n := 135) (d := 64)
      (constituentGraph_profile H ⟨256, 120, 56, 56⟩ h root true)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

end EPPAIII.Primitive
