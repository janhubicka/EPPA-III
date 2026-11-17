import EPPAIII.Primitive.RankThreeActionCatalogue
import EPPAIII.Primitive.SmallConstituentSourceModels

/-! # The triangular rows of Table 11.8 from their permutation action -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems SimpleGraph

/-- The rank-three permutation representation on two-element sets.
The chosen subgroup can be smaller than the full automorphism group. -/
def IsTriangularTwoSetAction {V : Type*} (H : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (labels : V ≃ TriangularVertex n) (P : Subgroup (Equiv.Perm V)),
    HasRankThreeGraphOrbits P H ∧
      ∀ p : P, ∃ q : Equiv.Perm (Fin n),
        ∀ x, labels (p.val x) = twoSetPerm q (labels x)

/-- A rank-three graph carrying the two-set action is the triangular
graph in one of its two complementary orientations. -/
theorem IsTriangularTwoSetAction.isModelUpToComplement {V : Type*} {H : SimpleGraph V}
    {n : ℕ} (h : IsTriangularTwoSetAction H n) (hn : 4 ≤ n)
    (hRank : HasRankThreeAutAction H) : IsModelUpToComplement H (triangularModel n) := by
  obtain ⟨labels, P, hOrbits, hPoint⟩ := h
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have distinct {x y : Fin n} (h : x.val ≠ y.val) : x ≠ y := fun he => h (congrArg Fin.val he)
  let e₀ := triangularPair a b (distinct (by simp [a, b]))
  let e₁ := triangularPair a c (distinct (by simp [a, c]))
  let e₂ := triangularPair c d (distinct (by simp [c, d]))
  have hEdge : (triangularModel n).Adj e₀ e₁ := by
    refine ⟨?_, a, by simp [e₀, triangularPair], by simp [e₁, triangularPair]⟩
    intro he
    have hb : b ∈ e₀.val := by simp [e₀, triangularPair]
    rw [he] at hb
    simp [e₁, triangularPair, a, b, c, Fin.ext_iff] at hb
  have hNonedge : e₀ ≠ e₂ ∧ ¬ (triangularModel n).Adj e₀ e₂ := by
    have ha : a ∈ e₀.val := by simp [e₀, triangularPair]
    have ha₂ : a ∉ e₂.val := by simp [e₂, triangularPair, a, c, d, Fin.ext_iff]
    refine ⟨fun he => ha₂ (he ▸ ha), ?_⟩
    rintro ⟨_, x, hx, hy⟩
    simp only [e₀, e₂, triangularPair, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> simp [a, b, c, d, Fin.ext_iff] at hy
  apply IsRankThreeActionModel.isModelUpToComplement ?_ hRank
  refine ⟨⟨e₀, e₁, hEdge⟩, ⟨e₀, e₂, hNonedge⟩, labels, P, hOrbits, ?_⟩
  intro p hp x y
  obtain ⟨q, hq⟩ := hPoint ⟨p, hp⟩
  change (triangularModel n).Adj (labels x) (labels y) ↔
    (triangularModel n).Adj (labels (p x)) (labels (p y))
  rw [hq x, hq y]
  exact twoSetPerm_automorphism q (labels x) (labels y)

private instance triangularActionAdj (n : ℕ) : DecidableRel (triangularModel n).Adj := by
  intro a b
  change Decidable (a ≠ b ∧ ∃ x : Fin n, x ∈ a.val ∧ x ∈ b.val)
  infer_instance

private abbrev triangularSourceOrientation (n : ℕ) (other : Bool) : SimpleGraph (TriangularVertex n) :=
  if other then triangularModel n else (triangularModel n)ᶜ

private instance triangularSourceOrientationAdj (n : ℕ) (other : Bool) :
    DecidableRel (triangularSourceOrientation n other).Adj := by
  cases other
  · exact inferInstanceAs (DecidableRel (triangularModel n)ᶜ.Adj)
  · exact triangularActionAdj n

private theorem triangularSource_width {p : SRGParameters} {n : ℕ} {other : Bool}
    (h : smallConstituentSourceModel p = some (.triangularComplement n, other)) : 4 ≤ n := by
  unfold smallConstituentSourceModel at h
  split at h <;> simp_all <;> omega

private theorem not_srg_of_degree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n k l μ : ℕ} (v : V) (h : G.degree v ≠ k) :
    ¬ G.IsSRGWith n k l μ := fun hSRG => h (hSRG.regular v)

private theorem not_srg_of_adjacent_codegree {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {n k l μ : ℕ} {x y : V} (hAdj : G.Adj x y)
    (h : Fintype.card (G.commonNeighbors x y) ≠ l) :
    ¬ G.IsSRGWith n k l μ := fun hSRG => h (hSRG.of_adj x y hAdj)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- The triangular rows have a unique orientation with the printed
parameters. T(7) and its complement have the same degree, so the
adjacent codegree decides that row. -/
private theorem triangularSource_excludes_other {p : SRGParameters} {n : ℕ} {other : Bool}
    (h : smallConstituentSourceModel p = some (.triangularComplement n, other)) :
    ¬ (triangularSourceOrientation n (!other)).IsSRGWith
      p.order p.degree p.adjacentCommon p.nonadjacentCommon := by
  unfold smallConstituentSourceModel at h
  split at h <;> simp_all
  all_goals obtain ⟨rfl, rfl⟩ := h
  · exact not_srg_of_degree (G := triangularModel 6) (k := 6) (triangularPair 0 1 (by decide)) (by decide)
  · exact not_srg_of_adjacent_codegree (G := (triangularModel 7)ᶜ)
      (x := triangularPair 0 1 (by decide)) (y := triangularPair 2 3 (by decide))
      (l := 5) (by decide) (by decide)
  · exact not_srg_of_degree (G := (triangularModel 8)ᶜ) (k := 12) (triangularPair 0 1 (by decide)) (by decide)
  · exact not_srg_of_degree (G := (triangularModel 11)ᶜ) (k := 18) (triangularPair 0 1 (by decide)) (by decide)
  · exact not_srg_of_degree (G := (triangularModel 12)ᶜ) (k := 20) (triangularPair 0 1 (by decide)) (by decide)

/-- The printed triangular permutation action and the SRG parameters
recover the exact orientation needed by the small-constituent screen. -/
theorem triangularSource_iso_of_action {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p : SRGParameters) {n : ℕ} {other : Bool}
    (hRank : HasRankThreeAutAction H)
    (hSRG : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hLabel : smallConstituentSourceModel p = some (.triangularComplement n, other))
    (hAction : IsTriangularTwoSetAction H n) :
    Nonempty (H ≃g if other then (SmallConstituentHostModel.triangularComplement n).graphᶜ
      else (SmallConstituentHostModel.triangularComplement n).graph) := by
  have hWrong := triangularSource_excludes_other hLabel
  rcases hAction.isModelUpToComplement (triangularSource_width hLabel) hRank with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · cases other
    · exact (hWrong (srg_of_iso φ hSRG)).elim
    · change Nonempty (H ≃g (triangularModel n)ᶜᶜ)
      simpa only [compl_compl] using (show Nonempty (H ≃g triangularModel n) from ⟨φ⟩)
  · cases other
    · exact ⟨φ⟩
    · exact (hWrong (srg_of_iso φ hSRG)).elim

/-- The five triangular Table 11.8 rows need only their natural
permutation representation on two-element sets. -/
def PublishedSmallTriangularActions : Prop :=
  ∀ {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (p : SRGParameters) (n : ℕ) (other : Bool),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentSourceModel p = some (.triangularComplement n, other) →
    IsTriangularTwoSetAction H n

/-- Recover a printed triangular model from the published action premise. -/
theorem PublishedSmallTriangularActions.source_model (hActions : PublishedSmallTriangularActions)
    {m : ℕ} (H : SimpleGraph (Fin m)) [DecidableRel H.Adj]
    (p : SRGParameters) {n : ℕ} {other : Bool}
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hSRG : H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hLabel : smallConstituentSourceModel p = some (.triangularComplement n, other)) :
    Nonempty (H ≃g if other then (SmallConstituentHostModel.triangularComplement n).graphᶜ
      else (SmallConstituentHostModel.triangularComplement n).graph) :=
  triangularSource_iso_of_action H p hRank hSRG hLabel
    (hActions H p n other hPrim hRank hSRG hLabel)

end EPPAIII.Primitive
