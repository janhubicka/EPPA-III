import EPPAIII.BlockSystems.RookThreeComplementEppa
import EPPAIII.EPPA.ProfileOrbitBound

/-!
# Actual R3 neighbourhood degrees under complement and reindexing

If w lies outside the chosen R3 copy in H, its neighbours among
the nine selected vertices become non-neighbours after complementing
both graphs. Reindexing the selected base by the explicit rook
self-complementing permutation preserves cardinalities.

Consequently the new outside cross-degree is exactly 9-k, where
k was the old one. This avoids a hidden assumption that one may
complement the host while keeping its selected graph unchanged:
both the host and the base are complemented and the base is
genuinely relabelled.
-/

namespace EPPAIII.BlockSystems

/-- The selected profile of an outside point in the complemented
rook EPPA embedding is exactly the permuted complement of its old
profile. This is a true equality of finite sets, not merely a
counting identity. -/
theorem rook_complement_reindexed_profile_eq
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (w : W) (hw : w ∈ finiteOutside e) :
    finiteNeighbourhoodProfile Hᶜ
      (EPPAIII.relabelEmbedding e rookComplementIndex) w =
        ((finiteNeighbourhoodProfile H e w)ᶜ).image
          rookComplementIndex.symm := by
  classical
  let p := rookComplementIndex
  let S := finiteNeighbourhoodProfile H e w
  let T := finiteNeighbourhoodProfile Hᶜ
    (EPPAIII.relabelEmbedding e p) w
  have hwNot : w ∉ Set.range e := by
    simpa [finiteOutside] using hw
  have hPoint (x : rookVertex) :
      x ∈ T ↔ p x ∉ S := by
    have hNe : w ≠ e (p x) := by
      intro h
      exact hwNot ⟨p x,h.symm⟩
    simp only [T,S,finiteNeighbourhoodProfile,
      Finset.mem_filter, Finset.mem_univ,true_and]
    change Hᶜ.Adj w (e (p x)) ↔
      ¬ H.Adj w (e (p x))
    simpa only [SimpleGraph.compl_adj,hNe,true_and]
  change T = (Sᶜ).image p.symm
  ext x
  constructor
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨p x, ?_, p.symm_apply_apply x⟩
    exact Finset.mem_compl.mpr ((hPoint x).mp hx)
  · intro hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
    have hyx' : y = p x := by
      have hh := congrArg p hyx
      simpa only [p.apply_symm_apply] using hh
    apply (hPoint x).mpr
    rw [← hyx']
    exact Finset.mem_compl.mp hy

/-- For every outside vertex, the two profile cardinalities sum
to nine, the size of the selected rook graph. -/
theorem rook_complement_reindexed_profile_card_sum_nine
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (w : W) (hw : w ∈ finiteOutside e) :
    (finiteNeighbourhoodProfile Hᶜ
        (EPPAIII.relabelEmbedding e rookComplementIndex) w).card +
      (finiteNeighbourhoodProfile H e w).card = 9 := by
  classical
  let S := finiteNeighbourhoodProfile H e w
  have hProfile :=
    rook_complement_reindexed_profile_eq H e w hw
  have hImageCard :
      ((Sᶜ).image rookComplementIndex.symm).card =
      (Sᶜ).card :=
    Finset.card_image_of_injective _ rookComplementIndex.symm.injective
  rw [hProfile,hImageCard]
  have hBound : S.card ≤ Fintype.card rookVertex := by
    simpa using Finset.card_le_univ S
  rw [Finset.card_compl]
  have hRook : Fintype.card rookVertex = 9 := by decide
  omega

end EPPAIII.BlockSystems
