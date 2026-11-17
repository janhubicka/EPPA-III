import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-! # Excluding a local graph with unique common neighbours on nonedges -/

namespace EPPAIII.Primitive
open SimpleGraph

private def closedNeighbors {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] (x : V) : Finset V :=
  insert x (J.neighborFinset x)

private theorem mem_closedNeighbors {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] (x y : V) :
    y ∈ closedNeighbors J x ↔ y = x ∨ J.Adj x y := by
  simp [closedNeighbors]

private theorem card_closedNeighbors {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] (x : V) :
    (closedNeighbors J x).card = J.degree x + 1 := by
  rw [closedNeighbors, Finset.card_insert_of_notMem, J.card_neighborFinset_eq_degree]
  simp

private theorem outside_card {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] (x : V) :
    (Finset.univ \ closedNeighbors J x).card = Fintype.card V - (J.degree x + 1) := by
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_closedNeighbors]

private theorem common_eq {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj]
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z)
    {a b} (hab : a ≠ b) (hnab : ¬ J.Adj a b) {x y}
    (hax : J.Adj a x) (hbx : J.Adj b x) (hay : J.Adj a y) (hby : J.Adj b y) :
    x = y := by
  obtain ⟨z, _, hz⟩ := hUnique a b hab hnab
  exact (hz x ⟨hax, hbx⟩).trans (hz y ⟨hay, hby⟩).symm

private theorem no_claw_of_unique_common {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z)
    {x a b c : V}
    (ha : J.Adj x a) (hb : J.Adj x b) (hc : J.Adj x c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hnab : ¬ J.Adj a b) (hnac : ¬ J.Adj a c) (hnbc : ¬ J.Adj b c) : False := by
  let S : Finset V := {a,b,c}
  let B (y : V) := (closedNeighbors J y).erase x
  have hN (y) (hy : y ∈ S) : J.Adj x y := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hNon (y) (hy : y ∈ S) (z) (hz : z ∈ S) (hne : y ≠ z) : ¬ J.Adj y z := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hy hz
    rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
    all_goals first | exact (hne rfl).elim | assumption | exact fun he => hnab he.symm |
      exact fun he => hnac he.symm | exact fun he => hnbc he.symm
  have hDisj : (↑S : Set V).PairwiseDisjoint B := by
    intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨hwX, hwY⟩ := Finset.mem_erase.mp hw
    obtain ⟨_, hwZ⟩ := Finset.mem_erase.mp hw'
    have hn := hNon y hy z hz hne
    obtain hwy | hwy := (mem_closedNeighbors J y w).mp hwY
    · subst w
      exact ((mem_closedNeighbors J z y).mp hwZ).elim hne (fun h => hn h.symm)
    obtain hwz | hwz := (mem_closedNeighbors J z w).mp hwZ
    · exact hn (hwz ▸ hwy)
    exact hwX (common_eq J hUnique hne hn hwy hwz (hN y hy).symm (hN z hz).symm)
  have hB (y) (hy : y ∈ S) : (B y).card = k-1 := by
    change ((closedNeighbors J y).erase x).card = k-1
    rw [Finset.card_erase_of_mem ((mem_closedNeighbors J y x).mpr (Or.inr (hN y hy).symm)),
      card_closedNeighbors, hReg]
    omega
  have hUnion : (S.biUnion B).card = 3*(k-1) := by
    rw [Finset.card_biUnion hDisj, Finset.sum_congr rfl hB]
    simp [S, hab, hac, hbc]
  have hSub : S.biUnion B ⊆ Finset.univ.erase x := by
    intro w hw
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ _⟩
  have hBound := Finset.card_le_card hSub
  rw [hUnion, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hCard] at hBound
  omega

private theorem nonadjacent_neighbors_of_unique_common {V : Type*} [Fintype V]
    (J : SimpleGraph V) [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 2 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z)
    (x : V) : ∃ a b, J.Adj x a ∧ J.Adj x b ∧ a ≠ b ∧ ¬ J.Adj a b := by
  by_contra h
  have hClique (a b : V) (ha : J.Adj x a) (hb : J.Adj x b) (hab : a ≠ b) : J.Adj a b := by
    by_contra hn
    exact h ⟨a, b, ha, hb, hab, hn⟩
  have hO : 0 < (Finset.univ \ closedNeighbors J x).card := by rw [outside_card, hCard, hReg]; omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hO
  have hy' := (mem_closedNeighbors J x y).not.mp (Finset.mem_sdiff.mp hy).2
  have hnotadj : ¬ J.Adj x y := fun h => hy' (Or.inr h)
  have hne : x ≠ y := fun h => hy' (Or.inl h.symm)
  obtain ⟨z, ⟨hxz, hyz⟩, _⟩ := hUnique x y hne hnotadj
  have hNeighbors : closedNeighbors J x ⊆ closedNeighbors J z := by
    intro w hw
    apply (mem_closedNeighbors J z w).mpr
    rcases (mem_closedNeighbors J x w).mp hw with rfl | hw
    · exact Or.inr hxz.symm
    by_cases hW : w = z
    · exact Or.inl hW
    · exact Or.inr (hClique z w hxz hw (Ne.symm hW))
  have hEq := Finset.eq_of_subset_of_card_le hNeighbors (by rw [card_closedNeighbors,
    card_closedNeighbors, hReg, hReg])
  exact (Finset.mem_sdiff.mp hy).2 (hEq.symm ▸ (mem_closedNeighbors J z y).mpr (Or.inr hyz.symm))

private structure LocalCliques {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (x : V) where
  left : Finset V
  right : Finset V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right
  union_eq : left ∪ right = J.neighborFinset x
  left_clique : J.IsClique ↑left
  right_clique : J.IsClique ↑right
  no_cross : ∀ a ∈ left, ∀ b ∈ right, ¬ J.Adj a b

private theorem localCliques_of_unique_common {V : Type*} [Fintype V]
    (J : SimpleGraph V) [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z)
    (x : V) : Nonempty (LocalCliques J x) := by
  obtain ⟨a, b, ha, hb, hab, hnab⟩ :=
    nonadjacent_neighbors_of_unique_common J (by omega) hCard hReg hUnique x
  let N := J.neighborFinset x
  let A := N ∩ closedNeighbors J a
  let B := N ∩ closedNeighbors J b
  have hA : a ∈ A := Finset.mem_inter.mpr ⟨(J.mem_neighborFinset x a).mpr ha,
    (mem_closedNeighbors J a a).mpr (Or.inl rfl)⟩
  have hB : b ∈ B := Finset.mem_inter.mpr ⟨(J.mem_neighborFinset x b).mpr hb,
    (mem_closedNeighbors J b b).mpr (Or.inl rfl)⟩
  have hDisjoint : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvB
    have hxv := (J.mem_neighborFinset x v).mp (Finset.mem_inter.mp hvA).1
    rcases (mem_closedNeighbors J a v).mp (Finset.mem_inter.mp hvA).2 with he | hva
    · subst v
      rcases (mem_closedNeighbors J b a).mp (Finset.mem_inter.mp hvB).2 with he | he
      · exact hab he
      · exact hnab he.symm
    rcases (mem_closedNeighbors J b v).mp (Finset.mem_inter.mp hvB).2 with rfl | hvb
    · exact hnab hva
    exact hxv.ne (common_eq J hUnique hab hnab hva hvb ha.symm hb.symm).symm
  have hCover : A ∪ B = N := by
    ext v
    constructor
    · intro hv
      exact (Finset.mem_union.mp hv).elim
        (fun hv => (Finset.mem_inter.mp hv).1) (fun hv => (Finset.mem_inter.mp hv).1)
    intro hv
    by_cases hva : v ∈ closedNeighbors J a
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hva⟩)
    by_cases hvb : v ∈ closedNeighbors J b
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hv, hvb⟩)
    have hva := (mem_closedNeighbors J a v).not.mp hva
    have hvb := (mem_closedNeighbors J b v).not.mp hvb
    exact (no_claw_of_unique_common J hk hCard hReg hUnique ha hb
      ((J.mem_neighborFinset x v).mp hv) hab
      (fun he => hva (Or.inl he.symm)) (fun he => hvb (Or.inl he.symm)) hnab
      (fun he => hva (Or.inr he)) (fun he => hvb (Or.inr he))).elim
  have hCluster (u v w : V) (hu : u ∈ N) (hv : v ∈ N) (hw : w ∈ N)
      (huv : J.Adj u v) (hvw : J.Adj v w) (huw : u ≠ w) : J.Adj u w := by
    by_contra hn
    have hEq := common_eq J hUnique huw hn huv hvw.symm
      ((J.mem_neighborFinset x u).mp hu).symm ((J.mem_neighborFinset x w).mp hw).symm
    exact ((J.mem_neighborFinset x v).mp hv).ne hEq.symm
  have hClique (v : V) (hv : v ∈ N) : J.IsClique ↑(N ∩ closedNeighbors J v) := by
    intro y hy z hz hyz
    obtain ⟨hyN, hyV⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp hy)
    obtain ⟨hzN, hzV⟩ := Finset.mem_inter.mp (Finset.mem_coe.mp hz)
    rcases (mem_closedNeighbors J v y).mp hyV with rfl | hyv
    · exact ((mem_closedNeighbors J y z).mp hzV).resolve_left (Ne.symm hyz)
    rcases (mem_closedNeighbors J v z).mp hzV with rfl | hzv
    · exact hyv.symm
    exact hCluster y v z hyN hv hzN hyv.symm hzv hyz
  refine ⟨⟨A, B, ⟨a, hA⟩, ⟨b, hB⟩, hDisjoint, hCover,
    hClique a ((J.mem_neighborFinset x a).mpr ha),
    hClique b ((J.mem_neighborFinset x b).mpr hb), ?_⟩⟩
  intro y hy z hz hyz
  obtain ⟨hyN, hyA⟩ := Finset.mem_inter.mp hy
  have hzN := (Finset.mem_inter.mp hz).1
  apply Finset.disjoint_left.mp hDisjoint _ hz
  apply Finset.mem_inter.mpr
  refine ⟨hzN, (mem_closedNeighbors J a z).mpr (Or.inr ?_)⟩
  rcases (mem_closedNeighbors J a y).mp hyA with rfl | hay
  · exact hyz
  have haz : a ≠ z := fun he => Finset.disjoint_left.mp hDisjoint hA (he.symm ▸ hz)
  exact hCluster a y z ((J.mem_neighborFinset x a).mpr ha) hyN hzN hay hyz haz

private theorem outside_card_eq_mul {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 3 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z)
    (x : V) (split : LocalCliques J x) :
    k = 2 * split.left.card * split.right.card := by
  let N := J.neighborFinset x
  let O := Finset.univ \ closedNeighbors J x
  let C (y : V) := J.neighborFinset y \ closedNeighbors J x
  rcases split with ⟨A, B, hANE, hBNE, hDisj, hCover, hACliq, hBCliq, hCross⟩
  change k = 2 * A.card * B.card
  change A ∪ B = N at hCover
  have hA (z : V) (hz : z ∈ A) : z ∈ N := hCover ▸ Finset.mem_union_left _ hz
  have hB (z : V) (hz : z ∈ B) : z ∈ N := hCover ▸ Finset.mem_union_right _ hz
  have hN : N.card = k-1 := by
    rw [show N = J.neighborFinset x from rfl, J.card_neighborFinset_eq_degree, hReg]
  have hSum : A.card + B.card = k-1 := by
    rw [← Finset.card_union_of_disjoint hDisj, hCover, ← hN]
  have hC (P Q : Finset V) (hpq : P.card + Q.card = k-1)
      (hP : P ⊆ N) (hPQ : P ∪ Q = N) (hPcl : J.IsClique ↑P)
      (hPQcross : ∀ y ∈ P, ∀ z ∈ Q, ¬ J.Adj y z) (y : V) (hy : y ∈ P) :
      (C y).card = Q.card := by
    have hxY : J.Adj x y := (J.mem_neighborFinset x y).mp (hP hy)
    have hxP : x ∉ P := by
      intro hx
      exact (J.mem_neighborFinset x x).mp (hP hx) |>.ne rfl
    have hInter : J.neighborFinset y ∩ closedNeighbors J x = insert x (P.erase y) := by
      ext z
      constructor
      · intro hz
        obtain ⟨hyz, hxz⟩ := Finset.mem_inter.mp hz
        have hyz := (J.mem_neighborFinset y z).mp hyz
        rcases (mem_closedNeighbors J x z).mp hxz with rfl | hxz
        · exact Finset.mem_insert_self _ _
        have hzN : z ∈ N := (J.mem_neighborFinset x z).mpr hxz
        have hz' : z ∈ P ∨ z ∈ Q := Finset.mem_union.mp (hPQ.symm ▸ hzN)
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyz.ne.symm,
          hz'.resolve_right (fun hz => hPQcross y hy z hz hyz)⟩)
      · intro hz
        rcases Finset.mem_insert.mp hz with he | hz
        · subst z
          exact Finset.mem_inter.mpr ⟨(J.mem_neighborFinset y x).mpr hxY.symm,
            (mem_closedNeighbors J x x).mpr (Or.inl rfl)⟩
        obtain ⟨hzy, hzP⟩ := Finset.mem_erase.mp hz
        exact Finset.mem_inter.mpr ⟨(J.mem_neighborFinset y z).mpr (hPcl hy hzP hzy.symm),
          (mem_closedNeighbors J x z).mpr (Or.inr ((J.mem_neighborFinset x z).mp (hP hzP)))⟩
    have hSize := Finset.card_sdiff_add_card_inter (J.neighborFinset y) (closedNeighbors J x)
    change (C y).card + _ = _ at hSize
    rw [hInter, Finset.card_insert_of_notMem (fun hm => hxP (Finset.mem_of_mem_erase hm)),
      Finset.card_erase_of_mem hy, J.card_neighborFinset_eq_degree, hReg] at hSize
    have hpos := Finset.card_pos.mpr ⟨y, hy⟩
    omega
  have hCA : ∀ y ∈ A, (C y).card = B.card :=
    hC A B hSum (fun _ hy => hA _ hy) hCover hACliq hCross
  have hCB : ∀ y ∈ B, (C y).card = A.card :=
    hC B A (by omega) (fun _ hy => hB _ hy) ((Finset.union_comm _ _).trans hCover) hBCliq
      (fun y hy z hz hyz => hCross z hz y hy hyz.symm)
  have hPairwise : (↑N : Set V).PairwiseDisjoint C := by
    intro y hy z hz hyz
    apply Finset.disjoint_left.mpr
    intro w hwY hwZ
    obtain ⟨hWY, hxW⟩ := Finset.mem_sdiff.mp hwY
    have hWZ := (Finset.mem_sdiff.mp hwZ).1
    have hxW' := (mem_closedNeighbors J x w).not.mp hxW
    have hEq := common_eq J hUnique (fun he => hxW' (Or.inl he.symm)) (fun e => hxW' (Or.inr e))
      ((J.mem_neighborFinset x y).mp hy) ((J.mem_neighborFinset y w).mp hWY).symm
      ((J.mem_neighborFinset x z).mp hz) ((J.mem_neighborFinset z w).mp hWZ).symm
    exact hyz hEq
  have hWhole : N.biUnion C = O := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hy
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
    · intro hy
      have hxY := (Finset.mem_sdiff.mp hy).2
      have hxY' := (mem_closedNeighbors J x y).not.mp hxY
      obtain ⟨z, ⟨hxz, hyz⟩, _⟩ := hUnique x y (fun he => hxY' (Or.inl he.symm))
        (fun e => hxY' (Or.inr e))
      exact Finset.mem_biUnion.mpr ⟨z, (J.mem_neighborFinset x z).mpr hxz,
        Finset.mem_sdiff.mpr ⟨(J.mem_neighborFinset z y).mpr hyz.symm, hxY⟩⟩
  have hO : O.card = k := by
    change (Finset.univ \ closedNeighbors J x).card = k
    rw [outside_card, hCard, hReg]
    omega
  rw [← hO, ← hWhole, Finset.card_biUnion hPairwise, ← hCover,
    Finset.sum_union hDisj, Finset.sum_congr rfl hCA, Finset.sum_congr rfl hCB]
  simp
  ring

private theorem no_geodetic_of_large_rook_orders {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 5 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z) : False := by
  obtain ⟨x⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨parts⟩ := localCliques_of_unique_common J (by omega) hCard hReg hUnique x
  have hCount := outside_card_eq_mul J (by omega) hCard hReg hUnique x parts
  have hSum : parts.left.card + parts.right.card = k-1 := by
    rw [← Finset.card_union_of_disjoint parts.disjoint, parts.union_eq,
      J.card_neighborFinset_eq_degree, hReg]
  have hA := Finset.card_pos.mpr parts.left_nonempty
  have hB := Finset.card_pos.mpr parts.right_nonempty
  have hSum' : parts.left.card + parts.right.card + 1 = k := by omega
  zify at hCount hSum' hA hB hk
  nlinarith [mul_nonneg (show 0 ≤ (parts.left.card : Int) - 1 by omega)
    (show 0 ≤ (parts.right.card : Int) - 1 by omega)]

private theorem unique_triangle_of_localCliques {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] (hReg : J.IsRegularOfDegree 3) (x : V)
    (parts : LocalCliques J x) : ∃! T : Finset V, T.card = 3 ∧ x ∈ T ∧ J.IsClique ↑T := by
  have hMake : ∀ (P Q : Finset V), P ∪ Q = J.neighborFinset x →
      (∀ y ∈ P, ∀ z ∈ Q, ¬ J.Adj y z) →
      J.IsClique ↑P → P.card = 2 → Q.card = 1 →
      ∃! T : Finset V, T.card = 3 ∧ x ∈ T ∧ J.IsClique ↑T := by
    intro P Q hCover hCross hP hP2 hQ1
    have hPN (v : V) (hv : v ∈ P) : J.Adj x v :=
      (J.mem_neighborFinset x v).mp (hCover ▸ Finset.mem_union_left _ hv)
    have hxP : x ∉ P := fun hx => (hPN x hx).ne rfl
    refine ⟨insert x P, ⟨by rw [Finset.card_insert_of_notMem hxP, hP2], Finset.mem_insert_self _ _, ?_⟩, ?_⟩
    · intro a ha b hb hneq
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha'
      · rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb'
        · exact (hneq rfl).elim
        · exact hPN b hb'
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp hb) with rfl | hb'
      · exact (hPN a ha').symm
      · exact hP ha' hb' hneq
    · intro T hT
      obtain ⟨hSize, hxT, hT⟩ := hT
      have hEr : (T.erase x).card = 2 := by rw [Finset.card_erase_of_mem hxT, hSize]
      obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < (T.erase x).card)
      have hSet : T.erase x = {a,b} := by
        apply Finset.eq_of_subset_of_card_le (t := T.erase x) ?_ ?_ |>.symm
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl
          · exact ha
          · exact hb
        · rw [hEr]; simp [hab]
      have hIn (v : V) (hv : v ∈ T.erase x) : v ∈ P ∨ v ∈ Q := by
        obtain ⟨hneq, hv'⟩ := Finset.mem_erase.mp hv
        have hAdj := hT hxT hv' hneq.symm
        exact Finset.mem_union.mp (hCover.symm ▸ (J.mem_neighborFinset x v).mpr hAdj)
      have hAdj := hT (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab
      have hSub : T.erase x ⊆ P := by
        rw [hSet]
        have hNoBoth (haQ : a ∈ Q) (hbQ : b ∈ Q) : False := by
          have := Finset.one_lt_card_iff.mpr ⟨a, b, haQ, hbQ, hab⟩
          omega
        rcases hIn a ha with haP | haQ <;> rcases hIn b hb with hbP | hbQ
        · intro v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          exact hv.elim (· ▸ haP) (· ▸ hbP)
        · exact (hCross a haP b hbQ hAdj).elim
        · exact (hCross b hbP a haQ hAdj.symm).elim
        · exact (hNoBoth haQ hbQ).elim
      have hEq : T.erase x = P := Finset.eq_of_subset_of_card_le hSub (by omega)
      rw [← hEq, Finset.insert_erase hxT]
  have hSum : parts.left.card + parts.right.card = 3 := by
    rw [← Finset.card_union_of_disjoint parts.disjoint, parts.union_eq,
      J.card_neighborFinset_eq_degree, hReg]
  have hA := Finset.card_pos.mpr parts.left_nonempty
  have hB := Finset.card_pos.mpr parts.right_nonempty
  by_cases hTwo : parts.left.card = 2
  · exact hMake parts.left parts.right parts.union_eq parts.no_cross
      parts.left_clique hTwo (by omega)
  · apply hMake parts.right parts.left ((Finset.union_comm _ _).trans parts.union_eq) ?_
      parts.right_clique (by omega) (by omega)
    exact fun y hy z hz ha => parts.no_cross z hz y hy ha.symm

private theorem no_geodetic_of_five_rook_order {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj]
    (hCard : Fintype.card V = 8) (hReg : J.IsRegularOfDegree 3)
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z) : False := by
  have hTriangle (x : V) : ∃! T : Finset V, T.card = 3 ∧ x ∈ T ∧ J.IsClique ↑T := by
    obtain ⟨parts⟩ := localCliques_of_unique_common J (k := 4) (by decide) hCard hReg hUnique x
    exact unique_triangle_of_localCliques J hReg x parts
  have hDisjoint (T U : Finset V) (hT : T.card = 3) (hU : U.card = 3)
      (hTC : J.IsClique ↑T) (hUC : J.IsClique ↑U) (hne : T ≠ U) : Disjoint T U := by
    apply Finset.disjoint_left.mpr
    intro x hxT hxU
    obtain ⟨Z, _, hZ⟩ := hTriangle x
    exact hne ((hZ T ⟨hT, hxT, hTC⟩).trans (hZ U ⟨hU, hxU, hUC⟩).symm)
  obtain ⟨x⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨T, ⟨hT, hxT, hTC⟩, _⟩ := hTriangle x
  have hFind (S : Finset V) (hS : S.card < Fintype.card V) : ∃ y, y ∉ S := by
    have hPos : 0 < (Finset.univ \ S).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hPos
    exact ⟨y, (Finset.mem_sdiff.mp hy).2⟩
  obtain ⟨y, hyT⟩ := hFind T (by omega)
  obtain ⟨U, ⟨hU, hyU, hUC⟩, _⟩ := hTriangle y
  have hTU := hDisjoint T U hT hU hTC hUC (fun he => hyT (he.symm ▸ hyU))
  have hSix : (T ∪ U).card = 6 := by rw [Finset.card_union_of_disjoint hTU, hT, hU]
  obtain ⟨z, hzTU⟩ := hFind (T ∪ U) (by omega)
  obtain ⟨W, ⟨hW, hzW, hWC⟩, _⟩ := hTriangle z
  have hTW := hDisjoint T W hT hW hTC hWC (fun he =>
    hzTU (Finset.mem_union_left _ (he.symm ▸ hzW)))
  have hUW := hDisjoint U W hU hW hUC hWC (fun he =>
    hzTU (Finset.mem_union_right _ (he.symm ▸ hzW)))
  have hTUW : Disjoint (T ∪ U) W := Finset.disjoint_union_left.mpr ⟨hTW, hUW⟩
  have hNine : ((T ∪ U) ∪ W).card = 9 := by rw [Finset.card_union_of_disjoint hTUW, hSix, hW]
  have hBound := Finset.card_le_univ ((T ∪ U) ∪ W)
  omega

/-- For a local graph of a square rook candidate of side `k + 1 ≥ 5`,
its order and degree preclude exactly one common neighbour at each nonedge. -/
theorem no_geodetic_of_rook_local_parameters {V : Type*} [Fintype V] (J : SimpleGraph V)
    [DecidableEq V] [DecidableRel J.Adj] {k : ℕ} (hk : 4 ≤ k)
    (hCard : Fintype.card V = 2*k) (hReg : J.IsRegularOfDegree (k-1))
    (hUnique : ∀ x y, x ≠ y → ¬ J.Adj x y → ∃! z, J.Adj x z ∧ J.Adj y z) : False := by
  by_cases hsmall : k = 4
  · subst k
    exact no_geodetic_of_five_rook_order J hCard hReg hUnique
  · exact no_geodetic_of_large_rook_orders J (by omega) hCard hReg hUnique

end EPPAIII.Primitive
