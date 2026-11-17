import EPPAIII.Primitive.BilinearGraph
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.Ring

/-! # Uniform induced obstructions in bilinear constituents -/

namespace EPPAIII.Primitive

open Matrix

private abbrev Seed := Matrix (Fin 2) (Fin 3) ℤ

private def pentagonSeed : Fin 5 → Seed :=
  ![!![0, 0, 1; 0, 1, 0],
    !![0, 0, 1; 0, 1, 1],
    !![0, 1, 0; 0, 1, 1],
    !![0, 1, 0; 1, 0, 0],
    !![1, 0, 0; 0, 1, 0]]

private def minor {R : Type*} [Ring R] {n : ℕ}
    (A : Matrix (Fin 2) (Fin n) R) (p q : Fin n) : R :=
  A 0 p * A 1 q - A 0 q * A 1 p

private def unitMinor (A : Seed) : Prop :=
  ∃ p q, minor A p q = 1 ∨ minor A p q = -1

private def rankOneSeed (A : Seed) : Prop :=
  ((∀ j, A 0 j = 0) ∨ (∀ j, A 1 j = 0) ∨ (∀ j, A 1 j = -A 0 j)) ∧
    ∃ r c, A r c = 1 ∨ A r c = -1

private def checkRankOneSeed (A : Seed) : Bool :=
  (((List.finRange 3).all (fun j => decide (A 0 j = 0)) ||
    (List.finRange 3).all (fun j => decide (A 1 j = 0))) ||
    (List.finRange 3).all (fun j => decide (A 1 j = -A 0 j))) &&
    (List.finRange 2).any (fun r =>
      (List.finRange 3).any (fun c => (A r c == 1) || (A r c == -1)))

private theorem checkRankOneSeed_sound {A : Seed} (h : checkRankOneSeed A = true) :
    rankOneSeed A := by
  unfold checkRankOneSeed at h
  unfold rankOneSeed
  obtain ⟨hRows, hEntry⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨?_, ?_⟩
  · rcases Bool.or_eq_true_iff.mp hRows with hZero | hOpp
    · rcases Bool.or_eq_true_iff.mp hZero with hFirst | hSecond
      · exact Or.inl (fun j => of_decide_eq_true
          (List.all_eq_true.mp hFirst j (List.mem_finRange j)))
      · exact Or.inr (Or.inl (fun j => of_decide_eq_true
          (List.all_eq_true.mp hSecond j (List.mem_finRange j))))
    · exact Or.inr (Or.inr (fun j => of_decide_eq_true
        (List.all_eq_true.mp hOpp j (List.mem_finRange j))))
  · obtain ⟨r, _, hr⟩ := List.any_eq_true.mp hEntry
    obtain ⟨c, _, hc⟩ := List.any_eq_true.mp hr
    exact ⟨r, c, (Bool.or_eq_true_iff.mp hc).imp beq_iff_eq.mp beq_iff_eq.mp⟩

private theorem seed_vertices : ∀ i, unitMinor (pentagonSeed i) := by
  unfold unitMinor
  decide

private theorem seed_edges : ∀ i j, (SimpleGraph.cycleGraph 5).Adj i j →
    rankOneSeed (pentagonSeed i - pentagonSeed j) := by
  have h : ∀ i j : Fin 5, (SimpleGraph.cycleGraph 5).Adj i j →
      checkRankOneSeed (pentagonSeed i - pentagonSeed j) = true := by decide
  exact fun i j hij => checkRankOneSeed_sound (h i j hij)

private theorem seed_nonedges : ∀ i j, i ≠ j → ¬ (SimpleGraph.cycleGraph 5).Adj i j →
    unitMinor (pentagonSeed i - pentagonSeed j) := by
  unfold unitMinor
  decide

private def liftSeed (F : Type*) [Field F] (m : ℕ) (A : Seed) :
    Matrix (Fin 2) (Fin m) F :=
  Matrix.of fun r c => if hc : c.val < 3 then (A r ⟨c.val, hc⟩ : F) else 0

private theorem liftSeed_sub {F : Type*} [Field F] {m : ℕ} (A B : Seed) :
    liftSeed F m (A - B) = liftSeed F m A - liftSeed F m B := by
  ext r c
  simp only [liftSeed, Matrix.of_apply, Matrix.sub_apply]
  split <;> simp_all

private theorem liftSeed_on_seed {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m)
    (A : Seed) (r : Fin 2) (c : Fin 3) :
    liftSeed F m A r (c.castLE hm) = (A r c : F) := by
  simp [liftSeed, c.isLt]

private theorem rank_two_of_minor {F : Type*} [Field F] {m : ℕ}
    (A : Matrix (Fin 2) (Fin m) F) (p q : Fin m) (h : minor A p q ≠ 0) :
    A.rank = 2 := by
  apply (bilinear_rank_two_iff_rows_independent A).mpr
  have hrows : A.row = ![A 0, A 1] := by
    funext r
    fin_cases r <;> rfl
  rw [hrows]
  apply LinearIndependent.pair_iff.mpr
  intro s t hlin
  have hp : s * A 0 p + t * A 1 p = 0 := congrFun hlin p
  have hq : s * A 0 q + t * A 1 q = 0 := congrFun hlin q
  have hs : s * minor A p q = 0 := by
    calc
      _ = (s * A 0 p + t * A 1 p) * A 1 q - (s * A 0 q + t * A 1 q) * A 1 p := by
          unfold minor
          ring
      _ = 0 := by rw [hp, hq]; simp
  have ht : t * minor A p q = 0 := by
    calc
      _ = A 0 p * (s * A 0 q + t * A 1 q) - A 0 q * (s * A 0 p + t * A 1 p) := by
          unfold minor
          ring
      _ = 0 := by rw [hp, hq]; simp
  exact ⟨(mul_eq_zero.mp hs).resolve_right h, (mul_eq_zero.mp ht).resolve_right h⟩

private theorem rank_two_of_seed {F : Type*} [Field F] {m : ℕ}
    (hm : 3 ≤ m) {A : Seed} (h : unitMinor A) : (liftSeed F m A).rank = 2 := by
  obtain ⟨p, q, hpq⟩ := h
  apply rank_two_of_minor _ (p.castLE hm) (q.castLE hm)
  rw [minor, liftSeed_on_seed hm, liftSeed_on_seed hm, liftSeed_on_seed hm, liftSeed_on_seed hm]
  have hz : ((minor A p q : ℤ) : F) ≠ 0 := by
    rcases hpq with h | h
    · simp [h]
    · simp [h]
  simpa only [minor, Int.cast_sub, Int.cast_mul] using hz

private theorem rank_one_of_seed {F : Type*} [Field F] {m : ℕ}
    (hm : 3 ≤ m) {A : Seed} (h : rankOneSeed A) : (liftSeed F m A).rank = 1 := by
  let B := liftSeed F m A
  obtain ⟨hrows, r, c, hentry⟩ := h
  have hB : B ≠ 0 := by
    intro hzero
    have hentry' : B r (c.castLE hm) ≠ 0 := by
      change liftSeed F m A r (c.castLE hm) ≠ 0
      rw [liftSeed_on_seed hm]
      rcases hentry with h | h <;> simp [h]
    exact hentry' (by rw [hzero]; rfl)
  rcases hrows with h | h | h
  · have hRow : A 0 = 0 := funext h
    have hzero : B 0 = 0 := by
      funext c
      simp [B, liftSeed, hRow]
    exact (bilinearFormsGraph_zero_adj_iff B).mp
      (bilinearFormsGraph_adj_of_same_row 0 hB.symm hzero.symm)
  · have hRow : A 1 = 0 := funext h
    have hzero : B 1 = 0 := by
      funext c
      simp [B, liftSeed, hRow]
    exact (bilinearFormsGraph_zero_adj_iff B).mp
      (bilinearFormsGraph_adj_of_same_row 1 hB.symm hzero.symm)
  · have hRow : A 1 = -A 0 := funext h
    have hopp : B 1 = -B 0 := by
      funext c
      simp only [B, liftSeed, Matrix.of_apply, Pi.neg_apply, hRow]
      split <;> simp
    have hne : B 0 ≠ 0 := by
      intro hzero
      apply hB
      have hzero' : B 1 = 0 := by rw [hopp, hzero, neg_zero]
      ext r c
      fin_cases r
      · exact congrFun hzero c
      · exact congrFun hzero' c
    by_contra hRank
    have hNotAdj : ¬ (bilinearFormsGraph F m).Adj 0 B := by
      rw [bilinearFormsGraph_zero_adj_iff]
      exact hRank
    have hTwo := (bilinearFormsGraph_zero_nonadj_iff B).mp ⟨hB, hNotAdj⟩
    have hRows : B.row = ![B 0, B 1] := by
      funext i
      fin_cases i <;> rfl
    have hi := (bilinear_rank_two_iff_rows_independent B).mp hTwo
    rw [hRows] at hi
    exact (LinearIndependent.pair_iff' hne).mp hi (-1) (by simpa using hopp.symm)

private def seedGraphEmbedding {ι F : Type*} [Field F] {m k : ℕ}
    (S : SimpleGraph ι) [DecidableRel S.Adj] [DecidableEq ι]
    (A : ι → Matrix (Fin 2) (Fin m) F) (hVertex : ∀ i, (A i).rank = k)
    (hEdge : ∀ i j, S.Adj i j → (A i - A j).rank = 1)
    (hNonedge : ∀ i j, i ≠ j → ¬ S.Adj i j → (A i - A j).rank = 2) :
    S ↪g (bilinearFormsGraph F m).induce {A | A.rank = k} := by
  let f (i : ι) : {B : Matrix (Fin 2) (Fin m) F // B.rank = k} := ⟨A i, hVertex i⟩
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j h
    by_contra hne
    have hEqual : A i = A j := congrArg Subtype.val h
    have hzero : (A i - A j).rank = 0 := by
      rw [hEqual, sub_self, Matrix.rank_zero]
    by_cases e : S.Adj i j
    · have := hEdge i j e
      omega
    · have := hNonedge i j hne e
      omega
  · intro i j
    change (A i - A j).rank = 1 ↔ S.Adj i j
    refine ⟨fun h => ?_, hEdge i j⟩
    by_contra hna
    by_cases hne : i = j
    · subst j
      rw [sub_self, Matrix.rank_zero] at h
      omega
    · have := hNonedge i j hne hna
      omega

/-- For every field and (m ≥ 3), the zero-root rank-two constituent
contains an induced pentagon. The certificate uses only its first three
columns and minors of absolute value one. -/
def bilinearRankTwo_fiveCycle {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m) :
    SimpleGraph.cycleGraph 5 ↪g bilinearFormsRankTwoGraph F m := by
  let A (i : Fin 5) : Matrix (Fin 2) (Fin m) F := liftSeed F m (pentagonSeed i)
  have hEdge (i j : Fin 5) (h : (SimpleGraph.cycleGraph 5).Adj i j) :
      (A i - A j).rank = 1 := by
    change (liftSeed F m (pentagonSeed i) - liftSeed F m (pentagonSeed j)).rank = 1
    rw [← liftSeed_sub]
    exact rank_one_of_seed hm (seed_edges i j h)
  have hNonedge (i j : Fin 5) (hne : i ≠ j) (h : ¬ (SimpleGraph.cycleGraph 5).Adj i j) :
      (A i - A j).rank = 2 := by
    change (liftSeed F m (pentagonSeed i) - liftSeed F m (pentagonSeed j)).rank = 2
    rw [← liftSeed_sub]
    exact rank_two_of_seed hm (seed_nonedges i j hne h)
  exact seedGraphEmbedding (SimpleGraph.cycleGraph 5) A
    (fun i => rank_two_of_seed hm (seed_vertices i)) hEdge hNonedge

private def pathSeed : Fin 4 → Seed :=
  ![!![1, 0, 0; 0, 0, 0],
    !![0, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, 0],
    !![0, 0, 0; 0, 0, 1]]

private instance : DecidableRel (SimpleGraph.pathGraph 4).Adj := fun _ _ =>
  decidable_of_iff _ SimpleGraph.pathGraph_adj.symm

private theorem path_vertices : ∀ i, rankOneSeed (pathSeed i) := by
  have h : ∀ i : Fin 4, checkRankOneSeed (pathSeed i) = true := by decide
  exact fun i => checkRankOneSeed_sound (h i)

private theorem path_edges : ∀ i j, (SimpleGraph.pathGraph 4).Adj i j →
    rankOneSeed (pathSeed i - pathSeed j) := by
  have h : ∀ i j : Fin 4, (SimpleGraph.pathGraph 4).Adj i j →
      checkRankOneSeed (pathSeed i - pathSeed j) = true := by decide
  exact fun i j hij => checkRankOneSeed_sound (h i j hij)

private theorem path_nonedges : ∀ i j, i ≠ j → ¬ (SimpleGraph.pathGraph 4).Adj i j →
    unitMinor (pathSeed i - pathSeed j) := by
  unfold unitMinor
  decide

/-- For every field and (m ≥ 3), the zero-root rank-one constituent
contains an induced path on four vertices. -/
def bilinearRankOne_inducedPath {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m) :
    SimpleGraph.pathGraph 4 ↪g bilinearFormsRankOneGraph F m := by
  let A (i : Fin 4) : Matrix (Fin 2) (Fin m) F := liftSeed F m (pathSeed i)
  have hEdge (i j : Fin 4) (h : (SimpleGraph.pathGraph 4).Adj i j) :
      (A i - A j).rank = 1 := by
    change (liftSeed F m (pathSeed i) - liftSeed F m (pathSeed j)).rank = 1
    rw [← liftSeed_sub]
    exact rank_one_of_seed hm (path_edges i j h)
  have hNonedge (i j : Fin 4) (hne : i ≠ j) (h : ¬ (SimpleGraph.pathGraph 4).Adj i j) :
      (A i - A j).rank = 2 := by
    change (liftSeed F m (pathSeed i) - liftSeed F m (pathSeed j)).rank = 2
    rw [← liftSeed_sub]
    exact rank_two_of_seed hm (path_nonedges i j hne h)
  exact seedGraphEmbedding (SimpleGraph.pathGraph 4) A
    (fun i => rank_one_of_seed hm (path_vertices i)) hEdge hNonedge


end EPPAIII.Primitive
