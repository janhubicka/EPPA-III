import EPPAIII.Primitive.FactorialStabilizer
import EPPAIII.Primitive.LocalReduction
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# The Gewirtz exclusion

The parameters supply regularity and triangle-freeness. The group input is
that the order of the pointwise stabilizer of each nonedge is prime to 3.
-/

namespace EPPAIII.Primitive

/-- The triangle-free case of the bound `R(3,3) ≤ 6`. -/
private theorem independentTriple_of_card_ge_six {V : Type*} (G : SimpleGraph V)
    (hTriangleFree : ∀ {a b c}, G.Adj a b → G.Adj a c → ¬ G.Adj b c)
    (T : Finset V) (hLarge : 6 ≤ T.card) :
    ∃ S ⊆ T, S.card = 3 ∧ G.induce (S : Set V) = ⊥ := by
  classical
  have triple (a b c : V) (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hab' : ¬ G.Adj a b) (hac' : ¬ G.Adj a c) (hbc' : ¬ G.Adj b c) :
      ∃ S ⊆ T, S.card = 3 ∧ G.induce (S : Set V) = ⊥ := by
    refine ⟨{a, b, c}, by simp [Finset.insert_subset_iff, ha, hb, hc],
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩, ?_⟩
    ext w z
    change G.Adj w.val z.val ↔ False
    have hw : w.val ∈ ({a, b, c} : Finset V) := w.property
    have hz : z.val ∈ ({a, b, c} : Finset V) := z.property
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw hz
    grind [G.adj_comm, G.loopless.irrefl]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  let A := (T.erase a).filter (G.Adj a)
  let B := (T.erase a).filter (fun x => ¬ G.Adj a x)
  have hSplit : A.card + B.card = T.card - 1 := by
    dsimp only [A, B]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem ha]
  by_cases hA : 2 < A.card
  · obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.mp hA
    obtain ⟨hbT, hbAdj⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcT, hcAdj⟩ := Finset.mem_filter.mp hc
    obtain ⟨hdT, hdAdj⟩ := Finset.mem_filter.mp hd
    exact triple b c d (Finset.mem_of_mem_erase hbT) (Finset.mem_of_mem_erase hcT)
      (Finset.mem_of_mem_erase hdT) hbc hbd hcd
      (hTriangleFree hbAdj hcAdj) (hTriangleFree hbAdj hdAdj) (hTriangleFree hcAdj hdAdj)
  · obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ :=
      Finset.two_lt_card_iff.mp (by omega : 2 < B.card)
    obtain ⟨hbT, hbNot⟩ := Finset.mem_filter.mp hb
    obtain ⟨hcT, hcNot⟩ := Finset.mem_filter.mp hc
    obtain ⟨hdT, hdNot⟩ := Finset.mem_filter.mp hd
    have pair (x y : V) (hx : x ∈ T.erase a) (hy : y ∈ T.erase a)
        (hax : ¬ G.Adj a x) (hay : ¬ G.Adj a y) (hxy : x ≠ y) (hn : ¬ G.Adj x y) :
        ∃ S ⊆ T, S.card = 3 ∧ G.induce (S : Set V) = ⊥ :=
      triple a x y ha (Finset.mem_of_mem_erase hx) (Finset.mem_of_mem_erase hy)
        (Finset.ne_of_mem_erase hx).symm (Finset.ne_of_mem_erase hy).symm hxy hax hay hn
    by_cases hbc' : G.Adj b c
    · by_cases hbd' : G.Adj b d
      · exact pair c d hcT hdT hcNot hdNot hcd (hTriangleFree hbc' hbd')
      · exact pair b d hbT hdT hbNot hdNot hbd hbd'
    · exact pair b c hbT hcT hbNot hcNot hbc hbc'

/-- EPPA for at least 28 vertices forces a factor of three in a nonedge stabilizer. -/
theorem gewirtz_not_eppa_embedding {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (h : H.IsSRGWith 56 10 0 2) (e : V ↪ W) (hLarge : 28 ≤ Nat.card V)
    (hStabilizer : ∀ v u, v ≠ u → ¬ H.Adj v u →
      ¬ 3 ∣ Nat.card (pointwiseGraphStabilizer H {v, u})) :
    ¬ IsEPPAEmbedding G H e := by
  classical
  intro heppa
  let _ : Fintype V := Fintype.ofFinite V
  have hV : 28 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hLarge
  have _ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let v : V := Classical.choice inferInstance
  have hDegree (x : V) : (G.neighborFinset x).card ≤ 10 := by
    let localMap : G.neighborSet x ↪ H.neighborSet (e x) :=
      restrictEmbedding e (fun y hy => (heppa.1 x y).mp hy)
    have hCard := Fintype.card_le_of_embedding localMap
    rwa [H.card_neighborSet_eq_degree, h.regular.degree_eq, G.card_neighborSet_eq_degree] at hCard
  have hFirst : (insert v (G.neighborFinset v)).card ≤ 11 :=
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hDegree v) 1)
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show (insert v (G.neighborFinset v)).card < (Finset.univ : Finset V).card by
      rw [Finset.card_univ]
      omega)
  have huv : v ≠ u := fun heq => hu (heq ▸ Finset.mem_insert_self _ _)
  have hNonedge : ¬ G.Adj v u := fun hadj =>
    hu (Finset.mem_insert_of_mem ((G.mem_neighborFinset _ _).mpr hadj))
  let banned := insert v (insert u (G.neighborFinset v ∪ G.neighborFinset u))
  let T : Finset V := Finset.univ \ banned
  have hBanned : banned.card ≤ 22 := by
    calc
      banned.card ≤ (insert u (G.neighborFinset v ∪ G.neighborFinset u)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (G.neighborFinset v ∪ G.neighborFinset u).card + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) _
      _ ≤ (G.neighborFinset v).card + (G.neighborFinset u).card + 1 + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ 22 := by have := hDegree v; have := hDegree u; omega
  have hT : 6 ≤ T.card := by
    dsimp only [T]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    omega
  have hTriangleFree {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
      False := by
    have hZero := h.of_adj _ _ ((heppa.1 a b).mp hab)
    have hPos : 0 < Fintype.card (H.commonNeighbors (e a) (e b)) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨e c, H.mem_commonNeighbors.mpr ⟨(heppa.1 a c).mp hac, (heppa.1 b c).mp hbc⟩⟩⟩
    omega
  obtain ⟨S, hSub, hSize, hIndependent⟩ :=
    independentTriple_of_card_ge_six G hTriangleFree T hT
  have hBan (x : V) (hx : x ∈ (S : Set V)) : x ∉ banned :=
    (Finset.mem_sdiff.mp (hSub hx)).2
  have hOutside (a : V) (ha : a ∈ ({v, u} : Finset V)) : a ∉ (S : Set V) := by
    intro hIn
    apply hBan a hIn
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [banned]
  have hNoAdj (a : V) (ha : a ∈ ({v, u} : Finset V)) (x : V) (hx : x ∈ (S : Set V)) :
      ¬ G.Adj a x := by
    intro hAdj
    apply hBan x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_left _ ((G.mem_neighborFinset _ _).mpr hAdj)))
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ ((G.mem_neighborFinset _ _).mpr hAdj)))
  have hOrder : 3 ≤ Nat.card (S : Set V) := by
    rw [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe, hSize]
  have hDiv := factorial_dvd_pointwiseStabilizer_card_of_homogeneous_subset
    G H e heppa {v, u} (S : Set V) hOutside
    (fun a ha x hx y hy => iff_of_false (hNoAdj a ha x hx) (hNoAdj a ha y hy))
    (Or.inr hIndependent) hOrder
  rw [Finset.coe_insert, Finset.coe_singleton, Set.image_pair] at hDiv
  exact hStabilizer (e v) (e u) (e.injective.ne huv) (fun hadj => hNonedge ((heppa.1 v u).mpr hadj))
    ((show 3 ∣ Nat.factorial 3 by decide).trans hDiv)

/-- The nonedge-stabilizer order given for the Gewirtz graph supplies the group input. -/
theorem gewirtz_maxEppaOrder_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h : H.IsSRGWith 56 10 0 2)
    (hStabilizer : ∀ v u, v ≠ u → ¬ H.Adj v u →
      Nat.card (pointwiseGraphStabilizer H {v, u}) = 32) :
    maxEppaOrder H ≤ 27 := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained H
  by_contra! hLarge
  exact gewirtz_not_eppa_embedding (H.induce S) H h
    (Function.Embedding.subtype S) (by omega)
    (by intro v u hne hnot; rw [hStabilizer v u hne hnot]; decide) heppa

end EPPAIII.Primitive
