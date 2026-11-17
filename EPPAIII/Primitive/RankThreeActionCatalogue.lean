import EPPAIII.Primitive.GraphTwoClosure
import EPPAIII.Primitive.PublishedRankThreeCoverage
import EPPAIII.Primitive.AffineLineExclusion

/-! # Reading the rank-three catalogue as permutation data -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open SimpleGraph

/-- A vertex labelling under which the same rank-three subgroup preserves
the host and one of the catalogue graphs. The model orientation may be
chosen independently of the host orientation. -/
def IsRankThreeActionModel {V W : Type*} (H : SimpleGraph V) (K : SimpleGraph W) : Prop :=
  (∃ a b, K.Adj a b) ∧ (∃ a b, a ≠ b ∧ ¬ K.Adj a b) ∧
    ∃ (labels : V ≃ W) (P : Subgroup (Equiv.Perm V)),
      HasRankThreeGraphOrbits P H ∧ P ≤ graphAutomorphisms (pullbackGraph K labels)

/-- A group-labelled catalogue model gives a graph isomorphism up to
complement. It suffices to identify the permutation action and the
invariance of the labelled model. -/
theorem IsRankThreeActionModel.isModelUpToComplement {V W : Type*}
    {H : SimpleGraph V} {K : SimpleGraph W} (hModel : IsRankThreeActionModel H K)
    (hRank : HasRankThreeAutAction H) : IsModelUpToComplement H K := by
  obtain ⟨⟨a, b, hEdge⟩, ⟨c, d, hcd, hNonedge⟩, labels, P, hOrbits, hPreserve⟩ := hModel
  have hPullEdge : ∃ x y, (pullbackGraph K labels).Adj x y := by
    refine ⟨labels.symm a, labels.symm b, ?_⟩
    simpa only [pullbackGraph, labels.apply_symm_apply] using hEdge
  have hPullNonedge : ∃ x y, x ≠ y ∧ ¬ (pullbackGraph K labels).Adj x y := by
    refine ⟨labels.symm c, labels.symm d, labels.symm.injective.ne hcd, ?_⟩
    simpa only [pullbackGraph, labels.apply_symm_apply] using hNonedge
  rcases hOrbits.invariant_graph_eq_or_compl hPreserve hRank.1 hRank.2.1
      hPullEdge hPullNonedge with hDirect | hCompl
  · subst H
    exact Or.inl ⟨⟨labels, Iff.rfl⟩⟩
  · subst H
    refine Or.inr ⟨⟨labels, ?_⟩⟩
    intro x y
    change (labels x ≠ labels y ∧ ¬ K.Adj (labels x) (labels y)) ↔
      (x ≠ y ∧ ¬ K.Adj (labels x) (labels y))
    rw [labels.injective.ne_iff]

/-- Use group-labelled entries for families recognized through a permutation
representation and direct graph entries for the other families. -/
def FinPublishedRankThreeActionCoverage : Prop :=
  ∀ {n : ℕ} (H : SimpleGraph (Fin n)),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    HasPublishedRankThreeModel H ∨ ∃ model : FiniteGraphModel,
      CompleteRankThreeCase model.2 ∧ IsRankThreeActionModel H model.2

/-- Convert group-labelled entries to the graph-level coverage used by
the small-witness classification. -/
theorem finPublishedRankThreeGraphCoverage_of_actions
    (hCoverage : FinPublishedRankThreeActionCoverage) : FinPublishedRankThreeGraphCoverage := by
  intro n H hPrim hRank
  obtain hDirect | ⟨model, hData, hAction⟩ := hCoverage H hPrim hRank
  · exact hDirect
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨model, hData, hAction.isModelUpToComplement hRank⟩))))

/-- A published affine semilinear description of the subgroup's 2-closure
gives the full host action required by the affine-line exclusion. -/
theorem affineLineAction_of_twoClosure {K F : Type*} [Field K] [Field F] [Algebra K F]
    {H : SimpleGraph F} {P : Subgroup (Equiv.Perm F)} (hOrbits : HasRankThreeGraphOrbits P H)
    (hClosure : ∀ q ∈ permTwoClosure P,
      ∃ a b : F, ∃ σ : F ≃ₐ[K] F, ∀ z, q z = a * σ z + b) : HasAffineLineAction K H := by
  rw [permTwoClosure_eq_graphAutomorphisms hOrbits] at hClosure
  exact hClosure

end EPPAIII.Primitive
