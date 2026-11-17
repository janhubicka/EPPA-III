import EPPAIII.Primitive.RookDensity
import EPPAIII.Primitive.RankThreeCatalog
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Large rook graphs are excluded

Two disjoint edges in the same orientation have no common host neighbour.
Two disjoint edges in opposite orientations have a common neighbour at the
row-column intersection. The shared abstract induced graph is two edges.
-/

namespace EPPAIII.Primitive

open RookDensity
open Finset

variable {n : ℕ}

/-- The adjacency matrix of two disjoint edges in their natural order. -/
private def pairAdj (i j : Fin 4) : Prop := i ≠ j ∧ i.val / 2 = j.val / 2

/-- An ordered induced copy of two disjoint edges. -/
structure TwoEdgeTuple {W : Type*} (H : SimpleGraph W) (u : Fin 4 → W) : Prop where
  injective : Function.Injective u
  adj : ∀ i j, H.Adj (u i) (u j) ↔ pairAdj i j

/-- Four vertices with the six prescribed adjacency relations form an induced matching. -/
theorem four_cells_match {W : Type*} (H : SimpleGraph W) {a b c d : W}
    (hab : H.Adj a b) (hcd : H.Adj c d)
    (hac : ¬ H.Adj a c) (had : ¬ H.Adj a d)
    (hbc : ¬ H.Adj b c) (hbd : ¬ H.Adj b d) :
    TwoEdgeTuple H ![a, b, c, d] := by
  have hba := (H.adj_comm a b).mp hab
  have hdc := (H.adj_comm c d).mp hcd
  have hca : ¬ H.Adj c a := fun h => hac ((H.adj_comm a c).mpr h)
  have hda : ¬ H.Adj d a := fun h => had ((H.adj_comm a d).mpr h)
  have hcb : ¬ H.Adj c b := fun h => hbc ((H.adj_comm b c).mpr h)
  have hdb : ¬ H.Adj d b := fun h => hbd ((H.adj_comm b d).mpr h)
  have hab' := H.ne_of_adj hab
  have hcd' := H.ne_of_adj hcd
  have hac' : a ≠ c := by rintro rfl; exact had hcd
  have had' : a ≠ d := by rintro rfl; exact hac hdc
  have hbc' : b ≠ c := by rintro rfl; exact hbd hcd
  have hbd' : b ≠ d := by rintro rfl; exact hbc hdc
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm hab', Ne.symm hac', Ne.symm had',
      Ne.symm hbc', Ne.symm hbd', Ne.symm hcd']
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pairAdj, hab, hba, hcd, hdc, hac, had, hbc, hbd, hca, hda, hcb, hdb]

private theorem rowAdj (r a b : Fin n) (h : a ≠ b) :
    (rookGraph n).Adj (r, a) (r, b) := by
  exact ⟨fun hEq => h (congrArg Prod.snd hEq), Or.inl rfl⟩

private theorem colAdj (r a b : Fin n) (h : a ≠ b) :
    (rookGraph n).Adj (a, r) (b, r) := by
  exact ⟨fun hEq => h (congrArg Prod.fst hEq), Or.inr rfl⟩

private theorem rook_not_adj {a b : Fin n × Fin n} (hRow : a.1 ≠ b.1)
    (hCol : a.2 ≠ b.2) :
    ¬ (rookGraph n).Adj a b :=
  fun h => h.2.elim hRow hCol

private theorem commonNeighbor_rowPair (r a b : Fin n) (h : a ≠ b)
    (z : Fin n × Fin n)
    (ha : (rookGraph n).Adj z (r, a)) (hb : (rookGraph n).Adj z (r, b)) :
    z.1 = r := by
  rcases ha.2 with hr | ha'
  · exact hr
  rcases hb.2 with hr | hb'
  · exact hr
  exact False.elim (h (ha'.symm.trans hb'))

private def squareTranspose (n : ℕ) : rookGraph n ≃g rookGraph n where
  toEquiv := Equiv.prodComm (Fin n) (Fin n)
  map_rel_iff' := by
    intro a b
    change ((a.2, a.1) ≠ (b.2, b.1) ∧ (a.2 = b.2 ∨ a.1 = b.1)) ↔
      (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2))
    simp only [ne_eq, Prod.ext_iff, and_comm, or_comm]

private theorem twoEdges_of_sameRows (S : Finset (Fin n × Fin n))
    (hSame : SameOrientation S) :
    ∃ u : Fin 4 → Fin n × Fin n, (∀ i, u i ∈ S) ∧ TwoEdgeTuple (rookGraph n) u ∧
      ¬ (∃ z, ∀ i, (rookGraph n).Adj z (u i)) := by
  obtain ⟨r, s, hrs, A, B, hA, hB, hCardA, hCardB, hDisj⟩ := hSame
  obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp hCardA
  obtain ⟨c, d, hcd, hCD⟩ := Finset.card_eq_two.mp hCardB
  subst A
  subst B
  have haA : a ∈ ({a, b} : Finset (Fin n)) := by simp
  have hbA : b ∈ ({a, b} : Finset (Fin n)) := by simp
  have hcB : c ∈ ({c, d} : Finset (Fin n)) := by simp
  have hdB : d ∈ ({c, d} : Finset (Fin n)) := by simp
  have hac : a ≠ c := by rintro rfl; exact disjoint_left.mp hDisj haA hcB
  have had : a ≠ d := by rintro rfl; exact disjoint_left.mp hDisj haA hdB
  have hbc : b ≠ c := by rintro rfl; exact disjoint_left.mp hDisj hbA hcB
  have hbd : b ≠ d := by rintro rfl; exact disjoint_left.mp hDisj hbA hdB
  have ha := (mem_row S r a).mp (hA (by simp))
  have hb := (mem_row S r b).mp (hA (by simp))
  have hc := (mem_row S s c).mp (hB (by simp))
  have hd := (mem_row S s d).mp (hB (by simp))
  refine ⟨![(r, a), (r, b), (s, c), (s, d)], ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · exact four_cells_match (rookGraph n) (rowAdj r a b hab) (rowAdj s c d hcd)
      (rook_not_adj hrs hac) (rook_not_adj hrs had) (rook_not_adj hrs hbc) (rook_not_adj hrs hbd)
  · rintro ⟨z, hz⟩
    have hr := commonNeighbor_rowPair r a b hab z (hz 0) (hz 1)
    have hs := commonNeighbor_rowPair s c d hcd z (hz 2) (hz 3)
    exact hrs (hr.symm.trans hs)

private theorem twoEdges_of_sameOrientation (S : Finset (Fin n × Fin n))
    (hSame : SameOrientation S ∨ SameOrientation (transpose S)) :
    ∃ u : Fin 4 → Fin n × Fin n, (∀ i, u i ∈ S) ∧ TwoEdgeTuple (rookGraph n) u ∧
      ¬ (∃ z, ∀ i, (rookGraph n).Adj z (u i)) := by
  rcases hSame with h | h
  · exact twoEdges_of_sameRows S h
  · obtain ⟨u, hu, hPair, hNo⟩ := twoEdges_of_sameRows (transpose S) h
    let φ := squareTranspose n
    refine ⟨fun i => φ (u i), ?_,
      ⟨φ.injective.comp hPair.injective, fun i j => φ.map_rel_iff.trans (hPair.adj i j)⟩, ?_⟩
    · intro i
      have hi := hu i
      rcases hCell : u i with ⟨r, c⟩
      rw [hCell] at hi
      change (u i).swap ∈ S
      rw [hCell]
      exact (mem_transpose S r c).mp hi
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := φ.surjective z
      exact hNo ⟨w, fun i => φ.map_rel_iff.mp (hz i)⟩

private theorem twoEdges_of_oppositeOrientation (S : Finset (Fin n × Fin n))
    (hSize : 2 * n < S.card) :
    ∃ u : Fin 4 → Fin n × Fin n, (∀ i, u i ∈ S) ∧ TwoEdgeTuple (rookGraph n) u ∧
      (∃ z, ∀ i, (rookGraph n).Adj z (u i)) := by
  obtain ⟨r, c, A, B, hA, hB, hCardA, hCardB⟩ := dense_oppositeOrientation S hSize
  obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.mp hCardA
  obtain ⟨s, t, hst, hST⟩ := Finset.card_eq_two.mp hCardB
  subst A
  subst B
  have ha := mem_sdiff.mp (hA (by simp : a ∈ ({a, b} : Finset (Fin n))))
  have hb := mem_sdiff.mp (hA (by simp : b ∈ ({a, b} : Finset (Fin n))))
  have hs := mem_sdiff.mp (hB (by simp : s ∈ ({s, t} : Finset (Fin n))))
  have ht := mem_sdiff.mp (hB (by simp : t ∈ ({s, t} : Finset (Fin n))))
  have hAc : a ≠ c := fun h => ha.2 (mem_singleton.mpr h)
  have hBc : b ≠ c := fun h => hb.2 (mem_singleton.mpr h)
  have hSr : s ≠ r := fun h => hs.2 (mem_singleton.mpr h)
  have hTr : t ≠ r := fun h => ht.2 (mem_singleton.mpr h)
  refine ⟨![(r, a), (r, b), (s, c), (t, c)], ?_, ?_, ⟨(r, c), ?_⟩⟩
  · intro i
    fin_cases i
    · exact (mem_row S r a).mp ha.1
    · exact (mem_row S r b).mp hb.1
    · exact (mem_transpose S c s).mp ((mem_row (transpose S) c s).mp hs.1)
    · exact (mem_transpose S c t).mp ((mem_row (transpose S) c t).mp ht.1)
  · exact four_cells_match (rookGraph n) (rowAdj r a b hab) (colAdj c s t hst)
      (rook_not_adj hSr.symm hAc) (rook_not_adj hTr.symm hAc)
      (rook_not_adj hSr.symm hBc) (rook_not_adj hTr.symm hBc)
  · intro i
    fin_cases i
    · exact rowAdj r c a hAc.symm
    · exact rowAdj r c b hBc.symm
    · exact colAdj c r s hSr.symm
    · exact colAdj c r t hTr.symm

/-- A graph EPPA selection cannot contain copies of two disjoint
edges with different common-neighbour profiles in the witness. -/
theorem not_eppa_of_twoEdgeTuples {W : Type*} (H : SimpleGraph W) (S : Set W)
    (u v : Fin 4 → S) (hu : TwoEdgeTuple H (fun i => (u i).val))
    (hv : TwoEdgeTuple H (fun i => (v i).val))
    (hNo : ¬ (∃ z, ∀ i, H.Adj z (u i).val))
    (hYes : ∃ z, ∀ i, H.Adj z (v i).val) :
    ¬ IsEPPAEmbedding (H.induce S) H (Function.Embedding.subtype S) := by
  classical
  intro hEppa
  have hU : Function.Injective u := fun i j h => hu.injective (congrArg Subtype.val h)
  have hV : Function.Injective v := fun i j h => hv.injective (congrArg Subtype.val h)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair u v hU hV
  let D := (univ : Finset (Fin 4)).image u
  have hPartial : IsPartialGraphAutomorphism (H.induce S) D p := by
    intro a b ha hb
    obtain ⟨i, _, rfl⟩ := mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := mem_image.mp hb
    rw [hp, hp]
    exact (hu.adj i j).trans (hv.adj i j).symm
  obtain ⟨q, hq, hExt⟩ := hEppa.2 D p hPartial
  obtain ⟨z, hz⟩ := hYes
  obtain ⟨w, rfl⟩ := q.surjective z
  apply hNo
  refine ⟨w, fun i => ?_⟩
  have hMap := hExt (u i) (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  change q (u i).val = (p (u i)).val at hMap
  rw [hp] at hMap
  exact (hq w (u i).val).mpr (hMap.symm ▸ hz i)

/-- Every selected EPPA subgraph of a square rook graph satisfies the
bound from the two orientation obstructions. -/
theorem rookGraph_eppa_card_le (S : Set (Fin n × Fin n))
    (hEppa : IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n)
      (Function.Embedding.subtype S)) :
    Nat.card S ≤ max (2 * n) (n + 6) := by
  classical
  let := Fintype.ofFinite S
  let T := S.toFinset
  have hCard : T.card = Nat.card S := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
  by_contra hTooLarge
  have hBig : max (2 * n) (n + 6) < T.card := by
    rw [hCard]
    exact lt_of_not_ge hTooLarge
  have hLinear := (le_max_left (2 * n) (n + 6)).trans_lt hBig
  obtain ⟨u, hu, hU, hNo⟩ := twoEdges_of_sameOrientation T (dense_sameOrientation T hBig)
  obtain ⟨v, hv, hV, hYes⟩ := twoEdges_of_oppositeOrientation T hLinear
  exact not_eppa_of_twoEdgeTuples (rookGraph n) S
    (fun i => ⟨u i, (Set.mem_toFinset.mp (hu i))⟩)
    (fun i => ⟨v i, (Set.mem_toFinset.mp (hv i))⟩) hU hV hNo hYes hEppa

/-- The (5×5) bound suffices for the first subconstituent of the
126-point alternating-socle example. -/
theorem rookFive_eppa_card_le_eleven (S : Set (Fin 5 × Fin 5))
    (hEppa : IsEPPAEmbedding ((rookGraph 5).induce S) (rookGraph 5)
      (Function.Embedding.subtype S)) :
    Nat.card S ≤ 11 :=
  rookGraph_eppa_card_le S hEppa

/-- No actual half-order selection in a rook graph of side at least five
has the extension property. -/
theorem rookGraph_not_eppa_half (S : Set (Fin n × Fin n))
    (hn : 5 ≤ n) (hSize : n * n ≤ 2 * Nat.card S) :
    ¬ IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n) (Function.Embedding.subtype S) := by
  intro hEppa
  have hMul := Nat.mul_le_mul_right n hn
  rcases le_max_iff.mp (rookGraph_eppa_card_le S hEppa) with h | h <;> omega

end EPPAIII.Primitive
