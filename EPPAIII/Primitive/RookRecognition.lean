import EPPAIII.Primitive.ClebschRecognition
import EPPAIII.Primitive.RankTwoLineRecognition
import EPPAIII.Primitive.RookLocalRecognition
import Mathlib.Logic.Equiv.Option

/-! # Recognizing square rook graphs -/

namespace EPPAIII.Primitive

open SimpleGraph EPPAIII.BlockSystems

private theorem eq_or_eq_of_card_two {V : Type*} [Fintype V]
    (hCard : Fintype.card V = 2) {a b : V} (hne : a ≠ b) (x : V) : x = a ∨ x = b := by
  classical
  let S : Finset V := {a, b}
  have hUniv : S = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by
    simp [S, hCard, hne])
  have hx : x ∈ S := by rw [hUniv]; simp
  simpa [S] using hx

private theorem nonedge_common_complete_of_rankThree {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {n degree l : ℕ} (h : H.IsSRGWith n degree l 2)
    (hRank : HasRankThreeAutAction H) (a b : V) (hab : a ≠ b) (hnab : ¬ H.Adj a b)
    {s t : H.commonNeighbors a b} (hst : H.Adj s.val t.val)
    (x y : V) (hxy : x ≠ y) (hnxy : ¬ H.Adj x y)
    (c d : H.commonNeighbors x y) (hcd : c ≠ d) : H.Adj c.val d.val := by
  classical
  obtain ⟨π, hπ, hπa, hπb⟩ := hRank.2.2.2 a b x y hab hxy (iff_of_false hnab hnxy)
  let image (z : H.commonNeighbors a b) : H.commonNeighbors x y :=
    ⟨π z.val, hπa ▸ (hπ a z.val).mp z.property.1, hπb ▸ (hπ b z.val).mp z.property.2⟩
  have hne : image s ≠ image t := fun he => hst.ne (π.injective (congrArg Subtype.val he))
  have hEdge : H.Adj (image s).val (image t).val := (hπ s.val t.val).mp hst
  rcases eq_or_eq_of_card_two (h.of_not_adj hxy hnxy) hne c with hc | hc <;>
    rcases eq_or_eq_of_card_two (h.of_not_adj hxy hnxy) hne d with hd | hd
  · exact (hcd (hc.trans hd.symm)).elim
  · simpa [hc, hd] using hEdge
  · simpa [hc, hd] using hEdge.symm
  · exact (hcd (hc.trans hd.symm)).elim

/-- Rank three forces the common neighbours of nonedges to be independent.
Otherwise every nonadjacent pair in the six-vertex local graph has a common
neighbour there, although the local degree two precludes this. -/
private theorem rook_common_nonedge_independent {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 16 6 2 2)
    (hRank : HasRankThreeAutAction H) (a b : V) (hab : a ≠ b) (hnab : ¬ H.Adj a b)
    (s t : H.commonNeighbors a b) : ¬ H.Adj s.val t.val := by
  classical
  intro hst
  have hCommon := nonedge_common_complete_of_rankThree H h hRank a b hab hnab hst
  let r := a
  let J := localGraph H r
  have hProfile := constituentGraph_profile H (⟨16, 6, 2, 2⟩ : SRGParameters) h r false
  have hSize : Fintype.card (H.neighborSet r) = 6 :=
    Nat.card_eq_fintype_card.symm.trans hProfile.1
  have hReg (x : H.neighborSet r) : (J.neighborFinset x).card = 2 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, ← J.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hProfile.2 x
  let x : H.neighborSet r := ⟨s.val, s.property.1⟩
  let N := J.neighborFinset x
  let M := N.biUnion (fun z => (J.neighborFinset z).erase x)
  have hM : M.card ≤ 2 := by
    calc
      _ ≤ ∑ z ∈ N, ((J.neighborFinset z).erase x).card := Finset.card_biUnion_le
      _ = 2 := by
        have he (z) (hz : z ∈ N) : ((J.neighborFinset z).erase x).card = 1 := by
          have hxz : J.Adj x z := (J.mem_neighborFinset x z).mp hz
          rw [Finset.card_erase_of_mem ((J.mem_neighborFinset z x).mpr hxz.symm), hReg z]
        rw [Finset.sum_congr rfl he]
        simp [N, hReg]
  have hCover : Finset.univ ⊆ insert x (N ∪ M) := by
    intro y _
    by_cases hxy : x = y
    · simp [hxy]
    by_cases hAdj : J.Adj x y
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ((J.mem_neighborFinset x y).mpr hAdj))
    have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
    let w : H.commonNeighbors x.val y.val := ⟨r, x.property.symm, y.property.symm⟩
    have hMany : 1 < Fintype.card (H.commonNeighbors x.val y.val) := by
      rw [h.of_not_adj hxy' hAdj]; decide
    obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hMany w
    let q : H.neighborSet r := ⟨z.val, hCommon x.val y.val hxy' hAdj w z hz.symm⟩
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨q, (J.mem_neighborFinset x q).mpr z.property.1,
        Finset.mem_erase.mpr ⟨Ne.symm hxy, (J.mem_neighborFinset q y).mpr z.property.2.symm⟩⟩))
  have hUpper : (insert x (N ∪ M)).card ≤ 5 := by
    calc
      _ ≤ (N ∪ M).card + 1 := Finset.card_insert_le _ _
      _ ≤ N.card + M.card + 1 := Nat.add_le_add_right (Finset.card_union_le N M) 1
      _ ≤ 5 := by have hN : N.card = 2 := hReg x; omega
  have hLower := Finset.card_le_card hCover
  rw [Finset.card_univ, hSize] at hLower
  omega

private theorem local_charts_of_independent_rook_nonedges {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {n k : ℕ} (hk : 0 < k)
    (h : H.IsSRGWith n (2 * k) (k - 1) 2)
    (hIndependent : ∀ a b, a ≠ b → ¬ H.Adj a b →
      ∀ s t : H.commonNeighbors a b, ¬ H.Adj s.val t.val) :
    ∀ r, Nonempty (localGraph H r ≃g cliqueUnion 2 k) := by
  classical
  intro r
  have hProfile := constituentGraph_profile H ⟨_, _, _, _⟩ h r false
  apply regularCluster_iso_cliqueUnion (localGraph H r) hk
  · exact Nat.card_eq_fintype_card.symm.trans hProfile.1
  · intro x
    rw [← (localGraph H r).card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hProfile.2 x
  · intro a b c hab hbc hac
    by_contra hnc
    have hne : a.val ≠ c.val := fun he => hac (Subtype.ext he)
    let x : H.commonNeighbors a.val c.val := ⟨r, a.property.symm, c.property.symm⟩
    let y : H.commonNeighbors a.val c.val := ⟨b.val, hab, hbc.symm⟩
    exact hIndependent a.val c.val hne hnc x y b.property

private def splitRookRoot {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    (r : V) : (H.neighborSet r ⊕ Hᶜ.neighborSet r) ≃ {v : V // v ≠ r} where
  toFun := fun
    | .inl a => ⟨a.val, (H.ne_of_adj a.property).symm⟩
    | .inr b => ⟨b.val, b.property.1.symm⟩
  invFun := fun v => if h : H.Adj r v.val then .inl ⟨v.val, h⟩
    else .inr ⟨v.val, v.property.symm, h⟩
  left_inv := by
    rintro (a | b)
    · have ha : H.Adj r a.val := a.property
      simp [ha]
    · have hb : ¬ H.Adj r b.val := b.property.2
      simp [hb]
  right_inv := by
    intro v
    by_cases h : H.Adj r v.val <;> simp [h]

private def rookAxes (k : ℕ) :
    Option (Fin k) × Option (Fin k) ≃ Option ((Fin 2 × Fin k) ⊕ (Fin k × Fin k)) where
  toFun := fun
    | (none, none) => none
    | (some i, none) => some (.inl (0, i))
    | (none, some j) => some (.inl (1, j))
    | (some i, some j) => some (.inr (i, j))
  invFun := fun
    | none => (none, none)
    | some (.inl (side, i)) => if side = 0 then (some i, none) else (none, some i)
    | some (.inr (i, j)) => (some i, some j)
  left_inv := by rintro ⟨i, j⟩; cases i <;> cases j <;> rfl
  right_inv := by
    rintro (_ | (⟨side, i⟩ | ⟨i, j⟩))
    · rfl
    · fin_cases side <;> rfl
    · rfl

private def optionRook (k : ℕ) : SimpleGraph (Option (Fin k) × Option (Fin k)) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.imp Eq.symm Eq.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private instance (k : ℕ) : DecidableRel (optionRook k).Adj := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)))

private theorem card_optionRook_neighbors {k : ℕ} (a : Option (Fin k) × Option (Fin k)) :
    Fintype.card ((optionRook k).neighborSet a) = 2 * k := by
  classical
  let e : ({i : Option (Fin k) // i ≠ a.1} ⊕ {j : Option (Fin k) // j ≠ a.2}) ≃
      (optionRook k).neighborSet a :=
    { toFun := fun
        | .inl i => ⟨(i.val, a.2), fun h => i.property (congrArg Prod.fst h).symm, Or.inr rfl⟩
        | .inr j => ⟨(a.1, j.val), fun h => j.property (congrArg Prod.snd h).symm, Or.inl rfl⟩
      invFun := fun b => if h : b.val.1 = a.1 then
        .inr ⟨b.val.2, fun he => b.property.1 (Prod.ext h.symm he.symm)⟩
        else .inl ⟨b.val.1, h⟩
      left_inv := by
        rintro (i | j)
        · simp [i.property]
        · simp
      right_inv := by
        intro b
        by_cases hb : b.val.1 = a.1
        · apply Subtype.ext
          simp [hb]
          exact Prod.ext hb.symm rfl
        · have hc : b.val.2 = a.2 := b.property.2.resolve_left (fun h => hb h.symm) |>.symm
          apply Subtype.ext
          simp [hb]
          exact Prod.ext rfl hc.symm }
  have rows : Fintype.card {i : Option (Fin k) // i ≠ a.1} = k := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe a.1)
    simp only [Fintype.card_option, Fintype.card_fin] at h
    omega
  have columns : Fintype.card {j : Option (Fin k) // j ≠ a.2} = k := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe a.2)
    simp only [Fintype.card_option, Fintype.card_fin] at h
    omega
  rw [← Fintype.card_congr e, Fintype.card_sum, rows, columns]
  omega

/-- The square rook graph is reconstructed from its local two-clique charts.
At a fixed root, the two local cliques supply the nonzero coordinates.
The other common neighbour of a row vertex and a column vertex is the
point with that coordinate pair. -/
theorem rook_iso_of_srg_and_local_charts {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {k : ℕ} (h : H.IsSRGWith ((k + 1) * (k + 1)) (2 * k) (k - 1) 2)
    (hCharts : ∀ r, Nonempty (localGraph H r ≃g cliqueUnion 2 k)) :
    Nonempty (H ≃g rookGraph (k + 1)) := by
  classical
  obtain ⟨r⟩ : Nonempty V := Fintype.card_pos_iff.mp (h.card ▸ Nat.mul_pos (by omega) (by omega))
  let J := Classical.choice (hCharts r)
  let row (i : Fin k) := J.symm (0, i)
  let col (j : Fin k) := J.symm (1, j)
  have row_edge (i i' : Fin k) (hne : i ≠ i') : H.Adj (row i).val (row i').val :=
    J.symm.map_adj_iff.mpr ⟨rfl, hne⟩
  have col_edge (j j' : Fin k) (hne : j ≠ j') : H.Adj (col j).val (col j').val :=
    J.symm.map_adj_iff.mpr ⟨rfl, hne⟩
  have different_axes (i j : Fin k) : (row i).val ≠ (col j).val := by
    intro e
    have hPair := J.symm.injective (Subtype.ext e : row i = col j)
    exact (by decide : (0 : Fin 2) ≠ 1) (congrArg Prod.fst hPair)
  have cross_exists (i j : Fin k) : ∃ z : Hᶜ.neighborSet r,
      H.Adj (row i).val z.val ∧ H.Adj (col j).val z.val := by
    have hn : ¬ H.Adj (row i).val (col j).val := fun ha =>
      (by decide : (0 : Fin 2) ≠ 1) ((J.symm.map_adj_iff.mp ha).1)
    let w : H.commonNeighbors (row i).val (col j).val :=
      ⟨r, (row i).property.symm, (col j).property.symm⟩
    have hTwo : 1 < Fintype.card (H.commonNeighbors (row i).val (col j).val) := by
      rw [h.of_not_adj (different_axes i j) hn]; decide
    obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hTwo w
    have hzr : r ≠ z.val := fun eq => hz (Subtype.ext eq.symm)
    have hzNon : ¬ H.Adj r z.val := by
      intro ha
      let b : H.neighborSet r := ⟨z.val, ha⟩
      have hFirst : (0 : Fin 2) = (J b).1 := by
        simpa only [row, RelIso.apply_symm_apply] using
          (J.map_adj_iff.mpr (show (localGraph H r).Adj (row i) b from z.property.1)).1
      have hSecond : (1 : Fin 2) = (J b).1 := by
        simpa only [col, RelIso.apply_symm_apply] using
          (J.map_adj_iff.mpr (show (localGraph H r).Adj (col j) b from z.property.2)).1
      exact (by decide : (0 : Fin 2) ≠ 1) (hFirst.trans hSecond.symm)
    exact ⟨⟨z.val, hzr, hzNon⟩, z.property.1, z.property.2⟩
  let cross (p : Fin k × Fin k) := Classical.choose (cross_exists p.1 p.2)
  have cross_row (i j : Fin k) : H.Adj (row i).val (cross (i,j)).val :=
    (Classical.choose_spec (cross_exists i j)).1
  have cross_col (i j : Fin k) : H.Adj (col j).val (cross (i,j)).val :=
    (Classical.choose_spec (cross_exists i j)).2
  have exclude_row_clique (a b : H.neighborSet r) (z : Hᶜ.neighborSet r)
      (hab : H.Adj a.val b.val) (haz : H.Adj a.val z.val) (hbz : H.Adj b.val z.val) : False := by
    let φ := Classical.choice (hCharts a.val)
    let x : H.neighborSet a.val := ⟨r, a.property.symm⟩
    let y : H.neighborSet a.val := ⟨b.val, hab⟩
    let w : H.neighborSet a.val := ⟨z.val, haz⟩
    have hxy : (φ x).1 = (φ y).1 :=
      (φ.map_adj_iff.mpr (show (localGraph H a.val).Adj x y from b.property)).1
    have hyw : (φ y).1 = (φ w).1 :=
      (φ.map_adj_iff.mpr (show (localGraph H a.val).Adj y w from hbz)).1
    have hne : (φ x).2 ≠ (φ w).2 := fun he =>
      z.property.1 (congrArg Subtype.val (φ.injective (Prod.ext (hxy.trans hyw) he)))
    exact z.property.2 (φ.map_adj_iff.mp ⟨hxy.trans hyw, hne⟩)
  have cross_injective : Function.Injective cross := by
    rintro ⟨i, j⟩ ⟨a, b⟩ e
    apply Prod.ext
    · by_contra hne
      exact exclude_row_clique (row i) (row a) (cross (i,j)) (row_edge i a hne)
        (cross_row i j) (e.symm ▸ cross_row a b)
    · by_contra hne
      exact exclude_row_clique (col j) (col b) (cross (i,j)) (col_edge j b hne)
        (cross_col i j) (e.symm ▸ cross_col a b)
  have cross_bijective : Function.Bijective cross := by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    refine ⟨cross_injective, ?_⟩
    rw [Fintype.card_prod, Fintype.card_fin, Hᶜ.card_neighborSet_eq_degree, h.compl.regular r]
    have hExpand : (k + 1) * (k + 1) = k*k + 2*k + 1 := by ring
    rw [hExpand]
    omega
  let crossEquiv := Equiv.ofBijective cross cross_bijective
  let labels := ((rookAxes k).trans (Equiv.optionCongr
    ((Equiv.sumCongr J.symm.toEquiv crossEquiv).trans (splitRookRoot H r)))).trans
      (Equiv.optionSubtypeNe r)
  have share_anchor (a : H.neighborSet r) (z w : Hᶜ.neighborSet r)
      (haz : H.Adj a.val z.val) (haw : H.Adj a.val w.val) (hne : z ≠ w) :
      H.Adj z.val w.val := by
    let φ := Classical.choice (hCharts a.val)
    let x : H.neighborSet a.val := ⟨r, a.property.symm⟩
    let y : H.neighborSet a.val := ⟨z.val, haz⟩
    let t : H.neighborSet a.val := ⟨w.val, haw⟩
    have hy : (φ x).1 ≠ (φ y).1 := by
      intro he
      have hne' : (φ x).2 ≠ (φ y).2 := fun he' =>
        z.property.1 (congrArg Subtype.val (φ.injective (Prod.ext he he')))
      exact z.property.2 (φ.map_adj_iff.mp ⟨he, hne'⟩)
    have ht : (φ x).1 ≠ (φ t).1 := by
      intro he
      have hne' : (φ x).2 ≠ (φ t).2 := fun he' =>
        w.property.1 (congrArg Subtype.val (φ.injective (Prod.ext he he')))
      exact w.property.2 (φ.map_adj_iff.mp ⟨he, hne'⟩)
    have hEq : (φ y).1 = (φ t).1 := by omega
    have hNe : (φ y).2 ≠ (φ t).2 := fun he =>
      hne (Subtype.ext (congrArg (fun b : H.neighborSet a.val => b.val) (φ.injective (Prod.ext hEq he))))
    exact φ.map_adj_iff.mp ⟨hEq, hNe⟩
  have hAdj (x y : Option (Fin k) × Option (Fin k)) (hxy : (optionRook k).Adj x y) :
      H.Adj (labels x) (labels y) := by
    rcases x with ⟨(_ | i), (_ | j)⟩ <;> rcases y with ⟨(_ | a), (_ | b)⟩ <;>
      simp [optionRook, Prod.ext_iff] at hxy
    · exact (col b).property
    · exact (row a).property
    · exact (col j).property.symm
    · exact col_edge j b hxy
    · exact hxy ▸ cross_col a j
    · exact (row i).property.symm
    · exact row_edge i a hxy
    · exact hxy ▸ cross_row i b
    · exact hxy.symm ▸ (cross_col i j).symm
    · exact hxy.symm ▸ (cross_row i j).symm
    · have hDistinct : cross (i,j) ≠ cross (a,b) := by
        intro he
        exact hxy.1 (congrArg Prod.fst (cross_injective he)) (congrArg Prod.snd (cross_injective he))
      rcases hxy.2 with hI | hJ
      · subst a
        exact share_anchor (row i) _ _ (cross_row i j) (cross_row i b) hDistinct
      · subst b
        exact share_anchor (col j) _ _ (cross_col i j) (cross_col a j) hDistinct
  let e : optionRook k ≃g H := {
    toEquiv := labels
    map_rel_iff' := by
      intro a b
      constructor
      · intro hab
        let f : (optionRook k).neighborSet a → H.neighborSet (labels a) :=
          fun z => ⟨labels z.val, hAdj a z.val z.property⟩
        have hBij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card _).mpr
          ⟨fun x y he => Subtype.ext (labels.injective (congrArg Subtype.val he)), by
            rw [card_optionRook_neighbors, H.card_neighborSet_eq_degree, h.regular]⟩
        obtain ⟨c, hc⟩ := hBij.surjective ⟨labels b, hab⟩
        have heq : c.val = b := labels.injective (congrArg Subtype.val hc)
        exact heq ▸ c.property
      · exact hAdj a b }
  let coord : Option (Fin k) ≃ Fin (k+1) := Fintype.equivFinOfCardEq (by simp)
  let f : optionRook k ≃g rookGraph (k+1) := {
    toEquiv := Equiv.prodCongr coord coord
    map_rel_iff' := by
      intro a b
      change ((coord a.1, coord a.2) ≠ (coord b.1, coord b.2) ∧
        (coord a.1 = coord b.1 ∨ coord a.2 = coord b.2)) ↔ (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2))
      simp only [ne_eq, Prod.ext_iff, coord.injective.eq_iff] }
  exact ⟨e.symm.trans f⟩

/-- The four-by-four rook host is determined by rank three and the
parameters `(16,6,2,2)`. -/
theorem rook_four_iso_of_parameters {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 16 6 2 2) (hRank : HasRankThreeAutAction H) :
    Nonempty (H ≃g rookGraph 4) :=
  rook_iso_of_srg_and_local_charts H (k := 3) h
    (local_charts_of_independent_rook_nonedges H (by decide) h
      (rook_common_nonedge_independent H h hRank))

open EPPAIII.BlockSystems

/-- Remaining printed model identities after the Clebsch and four-by-four
rook rows have been proved. -/
def PublishedSmallRankThreeModelsExceptClebschAndRookFour : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    m ≠ .foldedFiveCube → m ≠ .rook 4 false →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- The 18 remaining source identities provide the small-model premise. -/
theorem publishedSmallRankThreeModelsExceptClebsch_of_exceptClebschAndRookFour
    (hSource : PublishedSmallRankThreeModelsExceptClebschAndRookFour) :
    PublishedSmallRankThreeModelsExceptClebsch := by
  intro n H _ p m complementModel hPrim hRank hSRG hLabel hClebsch
  by_cases hRook : m = .rook 4 false
  · subst m
    have hp : p = ⟨16,6,2,2⟩ ∧ complementModel = false := by
      unfold smallConstituentSourceModel at hLabel
      split at hLabel <;> simp_all
    obtain ⟨rfl, rfl⟩ := hp
    change Nonempty (H ≃g rookGraph 4)
    exact rook_four_iso_of_parameters H hSRG hRank
  · exact hSource H p m complementModel hPrim hRank hSRG hLabel hClebsch hRook

/-- For a rook graph of side at least five, a local graph cannot have one
common neighbour for each nonedge. Rank three therefore makes the two
common neighbours of each host nonedge independent. -/
private theorem rook_large_common_nonedge_independent {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {k : ℕ} (hk : 4 ≤ k)
    (h : H.IsSRGWith ((k + 1) * (k + 1)) (2 * k) (k - 1) 2)
    (hRank : HasRankThreeAutAction H) (a b : V) (hab : a ≠ b) (hnab : ¬ H.Adj a b)
    (s t : H.commonNeighbors a b) : ¬ H.Adj s.val t.val := by
  classical
  intro hst
  have hCommon := nonedge_common_complete_of_rankThree H h hRank a b hab hnab hst
  let r := a
  let J := localGraph H r
  have hp := constituentGraph_profile H ⟨_, _, _, _⟩ h r false
  have hSize : Fintype.card (H.neighborSet r) = 2*k :=
    Nat.card_eq_fintype_card.symm.trans hp.1
  have hReg : J.IsRegularOfDegree (k-1) := by
    intro x
    rw [← J.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.2 x
  refine no_geodetic_of_rook_local_parameters J hk hSize hReg ?_
  intro x y hxy hnxy
  have hxy' : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  let w : H.commonNeighbors x.val y.val := ⟨r, x.property.symm, y.property.symm⟩
  have hCard := h.of_not_adj hxy' hnxy
  have hMany : 1 < Fintype.card (H.commonNeighbors x.val y.val) := by rw [hCard]; decide
  obtain ⟨z, hz⟩ := Fintype.exists_ne_of_one_lt_card hMany w
  let q : H.neighborSet r := ⟨z.val, hCommon x.val y.val hxy' hnxy w z hz.symm⟩
  refine ⟨q, ⟨z.property.1, z.property.2⟩, ?_⟩
  intro u hu
  let u' : H.commonNeighbors x.val y.val := ⟨u.val, hu.1, hu.2⟩
  rcases eq_or_eq_of_card_two hCard hz u' with he | he
  · exact Subtype.ext (congrArg (fun v : H.commonNeighbors x.val y.val => v.val) he)
  · exact (u.property.ne (congrArg (fun v : H.commonNeighbors x.val y.val => v.val) he).symm).elim

/-- The parameters and rank-three action recognize square rook graphs of
side at least five. The small case of side four has its own proof. -/
theorem rook_large_iso_of_parameters {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {k : ℕ} (hk : 4 ≤ k)
    (h : H.IsSRGWith ((k + 1) * (k + 1)) (2 * k) (k - 1) 2)
    (hRank : HasRankThreeAutAction H) : Nonempty (H ≃g rookGraph (k+1)) :=
  rook_iso_of_srg_and_local_charts H h
    (local_charts_of_independent_rook_nonedges H (by omega) h
      (rook_large_common_nonedge_independent H hk h hRank))

/-- Host identities still supplied by the printed catalogue after the
Clebsch host and all six rook hosts have been recognized. -/
def PublishedSmallRankThreeModelsExceptClebschAndRooks : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel) (complementModel : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (m, complementModel) →
    m ≠ .foldedFiveCube → (∀ side, m ≠ .rook side false) →
    Nonempty (H ≃g if complementModel then m.graphᶜ else m.graph)

/-- The remaining 13 printed identities give the former source interface. -/
theorem publishedSmallRankThreeModelsExceptClebschAndRookFour_of_exceptClebschAndRooks
    (hSource : PublishedSmallRankThreeModelsExceptClebschAndRooks) :
    PublishedSmallRankThreeModelsExceptClebschAndRookFour := by
  intro n H _ p m complementModel hPrim hRank hSRG hLabel hClebsch hRookFour
  by_cases hRook : ∃ side, m = .rook side false
  · obtain ⟨side, rfl⟩ := hRook
    have hProfile : 4 ≤ side - 1 ∧ complementModel = false ∧
        p = ⟨(side - 1 + 1) * (side - 1 + 1), 2 * (side - 1), side - 1 - 1, 2⟩ := by
      unfold smallConstituentSourceModel at hLabel
      split at hLabel <;> simp_all
      all_goals
        obtain ⟨he, _⟩ := hLabel
        subst side
        decide
    rcases hProfile with ⟨hSide, rfl, rfl⟩
    change Nonempty (H ≃g rookGraph side)
    have hEq : side - 1 + 1 = side := by omega
    rw [← hEq]
    exact rook_large_iso_of_parameters H (k := side - 1) hSide hSRG hRank
  · exact hSource H p m complementModel hPrim hRank hSRG hLabel hClebsch
      (fun s hs => hRook ⟨s, hs⟩)

end EPPAIII.Primitive
