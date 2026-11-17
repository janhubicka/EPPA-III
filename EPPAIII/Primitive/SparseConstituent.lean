import EPPAIII.CliqueCovers.CliqueUnionDegrees
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Sparse subconstituents versus generalized clique covers -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem index_eq_of_reachable {V I : Type*} {G : SimpleGraph V} (index : V → I)
    (hIndex : ∀ {v w}, G.Adj v w → index v = index w)
    {v w : V} (h : G.Reachable v w) : index v = index w := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => rfl
  | cons edge _ ih => exact (hIndex edge).trans ih

/-- Number of neighbours across a single diagonal cross block. -/
def coverDiagonalDegree (X : CrossType) (t : ℕ) : ℕ :=
  match X with
  | .empty => 0
  | .full => t
  | .matching => 1
  | .coMatching => t - 1

/-- The fibre inside the same side, the diagonal cross block, and the other
cross blocks account for all neighbours of a vertex. -/
theorem coverGraph_left_degree {s t : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj] (i : Fin s) (a : Fin t) :
    (coverGraph s t X Y).degree (left i a) =
      t - 1 + coverDiagonalDegree X t + (if Y then (s - 1) * t else 0) := by
  classical
  let L : Finset (CoverVertex s t) :=
    ({false} : Finset Bool) ×ˢ (({i} : Finset (Fin s)) ×ˢ (Finset.univ.erase a))
  let D : Finset (CoverVertex s t) :=
    ({true} : Finset Bool) ×ˢ (({i} : Finset (Fin s)) ×ˢ
      (Finset.univ.filter (X.rel a)))
  let O : Finset (CoverVertex s t) :=
    if Y then ({true} : Finset Bool) ×ˢ
      ((Finset.univ.erase i) ×ˢ (Finset.univ : Finset (Fin t))) else ∅
  have hNeighbors : (coverGraph s t X Y).neighborFinset (left i a) = L ∪ D ∪ O := by
    ext z
    rcases z with ⟨side, j, b⟩
    rw [mem_neighborFinset]
    change coverAdj X Y (left i a) (side, j, b) ↔ (side, j, b) ∈ L ∪ D ∪ O
    cases side <;> by_cases hj : j = i
    · subst j
      cases Y <;> simp [L, D, O, coverAdj, left, Finset.mem_product, ne_comm]
    · have hi : i ≠ j := Ne.symm hj
      cases Y <;> simp [L, D, O, coverAdj, left, Finset.mem_product, hj, hi]
    · subst j
      cases Y <;> simp [L, D, O, coverAdj, left, Finset.mem_product]
    · have hi : i ≠ j := Ne.symm hj
      cases Y <;> simp [L, D, O, coverAdj, left, Finset.mem_product, hj, hi]
  have hDisjointLD : Disjoint L D := by
    apply Finset.disjoint_left.mpr
    rintro ⟨side, j, b⟩ hL hD
    have hLside : side = false := Finset.mem_singleton.mp (Finset.mem_product.mp hL).1
    have hDside : side = true := Finset.mem_singleton.mp (Finset.mem_product.mp hD).1
    exact Bool.false_ne_true (hLside.symm.trans hDside)
  have hDisjointO : Disjoint (L ∪ D) O := by
    cases Y
    · simp [O]
    · apply Finset.disjoint_left.mpr
      rintro ⟨side, j, b⟩ hLD hO
      have hO' : side = true ∧ j ≠ i := by
        simpa [O, Finset.mem_product, and_comm] using hO
      rcases Finset.mem_union.mp hLD with hL | hD
      · have hLside : side = false := Finset.mem_singleton.mp (Finset.mem_product.mp hL).1
        exact Bool.false_ne_true (hLside.symm.trans hO'.1)
      · exact hO'.2 (Finset.mem_singleton.mp (Finset.mem_product.mp
          (Finset.mem_product.mp hD).2).1)
  have hD : (Finset.univ.filter (X.rel a)).card = coverDiagonalDegree X t := by
    cases X
    · have hf : (Finset.univ.filter (CrossType.empty.rel a)) = ∅ := by
        ext b
        simp [CrossType.rel]
      simp [hf, coverDiagonalDegree]
    · have hf : (Finset.univ.filter (CrossType.full.rel a)) = Finset.univ := by
        ext b
        simp [CrossType.rel]
      simp [hf, coverDiagonalDegree]
    · have hf : (Finset.univ.filter (CrossType.matching.rel a)) = {a} := by
        ext b
        simp [CrossType.rel, eq_comm]
      simp [hf, coverDiagonalDegree]
    · have hf : (Finset.univ.filter (CrossType.coMatching.rel a)) = Finset.univ.erase a := by
        ext b
        simp [CrossType.rel, ne_comm]
      simp [hf, coverDiagonalDegree]
  change ((coverGraph s t X Y).neighborFinset (left i a)).card = _
  rw [hNeighbors, Finset.card_union_of_disjoint hDisjointO,
    Finset.card_union_of_disjoint hDisjointLD]
  cases Y <;> simp [L, D, O, Finset.card_product, hD]

/-- Empty off-diagonal blocks separate the distinct clique indices. -/
theorem coverGraph_s_eq_one_of_connected_off_empty {s t : ℕ} (X : CrossType)
    (hConnected : (coverGraph s t X false).Connected) : s = 1 := by
  obtain ⟨⟨side, i, a⟩⟩ := hConnected.nonempty
  have hIndex {v w : CoverVertex s t} (h : (coverGraph s t X false).Adj v w) :
      v.2.1 = w.2.1 := by
    rcases h with h | h
    · exact h.2.1
    · by_contra hne
      simpa [hne] using h.2
  have hSingle (j : Fin s) : i = j :=
    index_eq_of_reachable (fun v : CoverVertex s t => v.2.1) hIndex
      (hConnected (left i a) (left j a))
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  by_contra hne
  let j₀ : Fin s := ⟨0, hs⟩
  let j₁ : Fin s := ⟨1, by omega⟩
  have heq : j₀ = j₁ := (hSingle j₀).symm.trans (hSingle j₁)
  exact Nat.zero_ne_one (congrArg Fin.val heq)

/-- A connected generalized cover has a vertex with degree at least half its
order minus one. -/
theorem coverGraph_connected_not_sparse {s t : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj]
    (hConnected : (coverGraph s t X Y).Connected) (d : ℕ)
    (hRegular : (coverGraph s t X Y).IsRegularOfDegree d) :
    2 * s * t ≤ 2 * d + 2 := by
  obtain ⟨⟨side, i, a⟩⟩ := hConnected.nonempty
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hDegree := (hRegular (left i a)).symm.trans (coverGraph_left_degree X Y i a)
  cases Y
  · have hs := coverGraph_s_eq_one_of_connected_off_empty X hConnected
    subst s
    simp at hDegree ⊢
    omega
  · have hBlock : s * t = (s - 1) * t + t := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    simp at hDegree
    rw [Nat.mul_assoc, hBlock, Nat.mul_add]
    omega

/-- Every complement of a cover contains an independent set indexed by the
vertices of one of its base cliques. -/
theorem coverGraph_compl_independent_embedding {s t : ℕ} (X : CrossType) (Y : Bool)
    (i : Fin s) : ∃ f : Fin t ↪ CoverVertex s t,
      ∀ a b, ¬(coverGraph s t X Y)ᶜ.Adj (f a) (f b) := by
  refine ⟨⟨left i, fun a b h => congrArg (fun v : CoverVertex s t => v.2.2) h⟩, ?_⟩
  intro a b h
  exact h.2 ((left_induced X Y i i a b).mpr ⟨rfl, fun hab => h.1 (congrArg (left i) hab)⟩)

/-- For the complement of a generalized cover, the size of the base clique
is at least half the order minus the complement degree. -/
theorem coverGraph_compl_degree_add_block {s t : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj]
    (i : Fin s) (a : Fin t) :
    s * t ≤ (coverGraph s t X Y)ᶜ.degree (left i a) + t := by
  classical
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have hBlock : s * t = (s - 1) * t + t := by
    rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ s)]
  have hDiag : coverDiagonalDegree X t ≤ t := by
    cases X <;> simp [coverDiagonalDegree, Nat.succ_le_of_lt ht]
  rw [degree_compl, coverVertex_card, coverGraph_left_degree X Y i a,
    Nat.mul_assoc, hBlock, Nat.mul_add]
  cases Y <;> simp <;> omega

/-- In the complementary orientation, degrees above one are at least
one quarter of the order. -/
theorem coverGraph_compl_quarter_order_le_degree {s t : ℕ} (X : CrossType) (Y : Bool)
    [DecidableRel (coverGraph s t X Y).Adj] (i : Fin s) (a : Fin t)
    (hDegree : 1 < (coverGraph s t X Y)ᶜ.degree (left i a)) :
    2 * s * t ≤ 4 * (coverGraph s t X Y)ᶜ.degree (left i a) := by
  classical
  have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have ht : 0 < t := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  by_cases hs₁ : s = 1
  · subst s
    rw [degree_compl, coverVertex_card, coverGraph_left_degree X Y i a] at hDegree ⊢
    cases X <;> cases Y <;> simp [coverDiagonalDegree] at hDegree ⊢ <;> omega
  · have hsize : 2 * t ≤ s * t := Nat.mul_le_mul_right t (by omega)
    have hBlock := coverGraph_compl_degree_add_block X Y i a
    rw [Nat.mul_assoc]
    omega

/-- Two vertices in one base clique become nonadjacent in the complement
and have all vertices of another base clique as common neighbours. -/
theorem commonNeighbor_card_ge_of_compl_cover_embedding
    {W : Type*} [Fintype W] (G : SimpleGraph W) [DecidableRel G.Adj]
    {s t : ℕ} (X : CrossType) (Y : Bool) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (f : (coverGraph s t X Y)ᶜ ↪g G) :
    ∃ x y : W, x ≠ y ∧ ¬ G.Adj x y ∧ t ≤ Fintype.card (G.commonNeighbors x y) := by
  classical
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hij : i ≠ j := fun e => Nat.zero_ne_one (congrArg Fin.val e)
  have hab : a ≠ b := fun e => Nat.zero_ne_one (congrArg Fin.val e)
  have hAB : (coverGraph s t X Y).Adj (left i a) (left i b) :=
    (left_induced X Y i i a b).mpr ⟨rfl, hab⟩
  have hCross (u v : Fin t) : (coverGraph s t X Y)ᶜ.Adj (left i u) (left j v) :=
    ⟨fun e => hij (congrArg (fun w : CoverVertex s t => w.2.1) e),
      fun h => hij ((left_induced X Y i j u v).mp h).1⟩
  refine ⟨f (left i a), f (left i b), f.injective.ne hAB.ne, fun h => ?_, ?_⟩
  · exact (f.map_rel_iff.mp h).2 hAB
  · let common (c : Fin t) : G.commonNeighbors (f (left i a)) (f (left i b)) :=
      ⟨f (left j c), f.map_rel_iff.mpr (hCross a c), f.map_rel_iff.mpr (hCross b c)⟩
    have hInj : Function.Injective common := fun c e h =>
      congrArg (fun w : CoverVertex s t => w.2.2) (f.injective (congrArg Subtype.val h))
    simpa using Fintype.card_le_of_injective common hInj

private theorem degree_eq_of_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (φ : G ≃g H) (v : V) : H.degree (φ v) = G.degree v := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (φ.mapNeighborSet v)).symm

/-- Connected graphs of positive degree less than half their order minus
one are neither equal-clique unions nor their complements. -/
theorem sparseConnected_not_cliqueUnion_or_compl {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hConnected : G.Connected)
    (hRegular : G.IsRegularOfDegree d) (hPos : 0 < d)
    (hSparse : 2 * d + 2 < Fintype.card V) {s t : ℕ}
    (h : Nonempty (G ≃g cliqueUnion s t) ∨ Nonempty (G ≃g (cliqueUnion s t)ᶜ)) : False := by
  classical
  have hOrder : Fintype.card (Fin s × Fin t) = s * t := by simp
  rcases h with h | h
  · obtain ⟨φ⟩ := h
    have hSize := φ.card_eq.trans hOrder
    have hConn := φ.connected_iff.mp hConnected
    obtain ⟨⟨i, a⟩⟩ := hConn.nonempty
    have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hDeg := degree_eq_of_iso φ.symm (i, a)
    rw [hRegular, CliqueCovers.cliqueUnion_degree hs] at hDeg
    have hSingle : s = 1 := by
      by_contra hne
      let j₀ : Fin s := ⟨0, hs⟩
      let j₁ : Fin s := ⟨1, by omega⟩
      have hEq : j₀ = j₁ := index_eq_of_reachable (G := cliqueUnion s t) Prod.fst
        (fun edge => edge.1) (hConn (j₀, a) (j₁, a))
      exact Nat.zero_ne_one (congrArg Fin.val hEq)
    simp [hSingle] at hSize
    omega
  · obtain ⟨φ⟩ := h
    have hSize := φ.card_eq.trans hOrder
    obtain ⟨v⟩ := hConnected.nonempty
    let w := φ v
    have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le _) w.1.isLt
    have hDeg := degree_eq_of_iso φ v
    rw [CliqueCovers.cliqueUnion_compl_regular (φ v), hRegular] at hDeg
    have hs₂ : 2 ≤ s := by
      by_contra! hsmall
      have hs₁ : s = 1 := by omega
      simp [hs₁] at hDeg
      omega
    have hBlock : s * t = (s - 1) * t + t := by
      rw [← Nat.add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ s)]
    have ht : t ≤ (s - 1) * t := by
      simpa using Nat.mul_le_mul_right t (show 1 ≤ s - 1 by omega)
    omega

/-- A connected regular graph of degree less than half its order minus one
cannot be isomorphic to a generalized cover. -/
theorem sparseConnected_not_cover {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hConnected : G.Connected)
    (hRegular : G.IsRegularOfDegree d) (hSparse : 2 * d + 2 < Fintype.card V)
    {s t : ℕ} (X : CrossType) (Y : Bool) (φ : G ≃g coverGraph s t X Y) : False := by
  classical
  have hCard := φ.card_eq.trans (coverVertex_card s t)
  have hCoverReg (v : CoverVertex s t) : (coverGraph s t X Y).degree v = d := by
    simpa using ((degree_eq_of_iso φ (φ.symm v)).trans (hRegular (φ.symm v)))
  have hDegree := coverGraph_connected_not_sparse X Y (φ.connected_iff.mp hConnected) d hCoverReg
  omega

/-- An upper bound on independent-set size, together with the cover degree
formula, excludes the complementary cover orientation. -/
theorem not_compl_cover_of_independence_gap {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d b : ℕ} (hRegular : G.IsRegularOfDegree d)
    (hIndependent : ∀ {k : ℕ} (f : Fin k ↪ V), (∀ a b, ¬ G.Adj (f a) (f b)) → k ≤ b)
    (hGap : 2 * (d + b) < Fintype.card V)
    {s t : ℕ} (X : CrossType) (Y : Bool) (φ : G ≃g (coverGraph s t X Y)ᶜ) : False := by
  classical
  have hCard := φ.card_eq.trans (coverVertex_card s t)
  have hPos : 0 < Fintype.card (CoverVertex s t) := by rw [← φ.card_eq]; omega
  obtain ⟨⟨side, i, a⟩⟩ := Fintype.card_pos_iff.mp hPos
  have hDegree := degree_eq_of_iso φ.symm (left i a)
  rw [hRegular] at hDegree
  have hBlock := coverGraph_compl_degree_add_block X Y i a
  rw [← hDegree] at hBlock
  obtain ⟨f, hf⟩ := coverGraph_compl_independent_embedding X Y i
  have ht : t ≤ b := hIndependent (f.trans φ.symm.toEquiv.toEmbedding) (by
    intro x y h
    exact hf x y (φ.symm.map_rel_iff.mp h))
  rw [Nat.mul_assoc] at hCard
  omega

/-- Every generalized cover has even order, independently of its orientation. -/
theorem order_even_of_cover_or_compl {V : Type*} [Fintype V] (G : SimpleGraph V)
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (h : Nonempty (G ≃g coverGraph s t X Y) ∨ Nonempty (G ≃g (coverGraph s t X Y)ᶜ)) :
    Fintype.card V % 2 = 0 := by
  have hCard : Fintype.card V = 2 * s * t := by
    rcases h with h | h
    · obtain ⟨φ⟩ := h
      exact φ.card_eq.trans (coverVertex_card s t)
    · obtain ⟨φ⟩ := h
      exact φ.card_eq.trans (coverVertex_card s t)
  rw [Nat.mul_assoc] at hCard
  omega

/-- A connected regular graph whose degree is between two and a quarter of its
order has none of the four forms in the reduced Section 8 hypothesis. -/
theorem sparseConnected_excludes_cliqueUnion_or_cover {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hConnected : G.Connected)
    (hRegular : G.IsRegularOfDegree d) (hDegree : 1 < d)
    (hQuarter : 4 * d < Fintype.card V) :
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  have hSparse : 2 * d + 2 < Fintype.card V := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t
    exact ⟨fun φ => sparseConnected_not_cliqueUnion_or_compl G hConnected hRegular
      (by omega) hSparse (Or.inl ⟨φ⟩)⟩
  · intro s t
    exact ⟨fun φ => sparseConnected_not_cliqueUnion_or_compl G hConnected hRegular
      (by omega) hSparse (Or.inr ⟨φ⟩)⟩
  · intro s t X Y
    exact ⟨sparseConnected_not_cover G hConnected hRegular hSparse X Y⟩
  · intro s t X Y
    refine ⟨fun φ => ?_⟩
    obtain ⟨v⟩ := hConnected.nonempty
    obtain ⟨_, i, a⟩ := φ v
    have hOrder := φ.card_eq.trans (coverVertex_card s t)
    have hDeg := degree_eq_of_iso φ.symm (left i a)
    rw [hRegular] at hDeg
    have hLower := coverGraph_compl_quarter_order_le_degree X Y i a (hDeg ▸ hDegree)
    omega

end EPPAIII.Primitive
