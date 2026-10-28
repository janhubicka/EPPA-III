import EPPAIII.BlockSystems.RankThreeImprimitiveHomogeneity

/-!
# Rank-three imprimitivity with the actual Section 6 block hypotheses

The rank-three ordered-pair lemma was stated using explicit
same-block and different-block pairs. The printed imprimitive
host hypotheses supply precisely these witnesses: at least two
distinct nonempty block labels, and one block containing at
least two vertices.

This file extracts the witnesses from the standard finite
block cardinality assumptions and packages the consequence
with the same interface as the EPPA III block-system theorems.
No graph classification or EPPA is required.
-/

namespace EPPAIII.BlockSystems

/-- The concrete nontriviality conditions on an actual finite
invariant block system are enough to conclude homogeneity
of a vertex-transitive rank-three host. -/
theorem transitive_rank_three_actual_blocks_isHomogeneous
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPairs : HasOrderedPairOrbitByStatus H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    EPPAIII.DoubleCover.IsHomogeneousGraph H := by
  classical
  obtain ⟨b₀,hb₀⟩ := hNontrivial
  let S : Finset W := (Finset.univ : Finset W).filter
    (fun w => block w = b₀)
  have hCard : 1 < S.card := by
    dsimp [S]
    omega
  obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp hCard
  have huB : block u = b₀ := (Finset.mem_filter.mp hu).2
  have hvB : block v = b₀ := (Finset.mem_filter.mp hv).2
  have hInside : ∃ a b : W, a ≠ b ∧ block a = block b :=
    ⟨u,v,huv,huB.trans hvB.symm⟩
  have hMany : 1 < Fintype.card B := by omega
  obtain ⟨b₁,hDiffB⟩ :=
    Fintype.exists_ne_of_one_lt_card hMany b₀
  obtain ⟨w₀,hw₀⟩ := hSurj b₀
  obtain ⟨w₁,hw₁⟩ := hSurj b₁
  have hOutside : ∃ a b : W, block a ≠ block b := by
    refine ⟨w₀,w₁,?_⟩
    rw [hw₀,hw₁]
    exact Ne.symm hDiffB
  exact transitive_rank_three_imprimitive_isHomogeneous
    H block hBlocks hTrans hPairs hInside hOutside

/-- A non-homogeneous transitive host with an actual nontrivial
invariant partition cannot have the ordered-pair orbit
property of a rank-three action. This is precisely the final
contradiction used after the separate small-witness theorem. -/
theorem nonhomogeneous_imprimitive_not_rank_three_pairs
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hNonhom : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    ¬ HasOrderedPairOrbitByStatus H := by
  intro hPairs
  exact hNonhom (transitive_rank_three_actual_blocks_isHomogeneous
    H block hBlocks hSurj hTrans hPairs hManyBlocks hNontrivial)

end EPPAIII.BlockSystems
