import EPPAIII.CliqueCovers.FullMaskOrbit

/-!
# Normal forms of s full-clique neighbourhood masks

Suppose s outside twin classes have full/empty adjacency masks to the
s selected K_t's, each mask has size r, and every r-subset of the
selected clique indices occurs among these outside classes.

The binomial orbit bound forces r = 0,1,s-1 or s. For r=0 and s the
mask is uniformly empty/full. For r=1 and s-1 the outside classes can
be reindexed by a permutation of Fin s so the masks are exactly the
singleton or co-singleton masks.

This purely finite-set statement is the remaining mask normalization
needed for the zero-partial branch of Lemma 3.7. The EPPA action on
actual twin quotient classes supplies the hypotheses separately.
-/

namespace EPPAIII.CliqueCovers

/-- If all singleton masks occur in an s-indexed family, then
there is a permutation of the indices putting the masks into
their canonical singleton form. -/
theorem singleton_mask_family_reindex {s : ℕ}
    (mask : Fin s → Finset (Fin s))
    (hCover : ∀ j : Fin s, ∃ i : Fin s, mask i = {j}) :
    ∃ p : Equiv.Perm (Fin s),
      ∀ j : Fin s, mask (p j) = {j} := by
  classical
  let f : Fin s → Fin s := fun j => (hCover j).choose
  have hf (j : Fin s) : mask (f j) = {j} :=
    (hCover j).choose_spec
  have hInj : Function.Injective f := by
    intro i j hij
    have hMasks := congrArg mask hij
    rw [hf i, hf j] at hMasks
    have hi : i ∈ ({j} : Finset (Fin s)) := by
      rw [← hMasks]
      simp
    simpa using hi
  have hBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hInj, by simp⟩
  exact ⟨Equiv.ofBijective f hBij, hf⟩

/-- Similarly, all co-singleton masks can be reindexed
so the omitted coordinate is the class index. -/
theorem cosingleton_mask_family_reindex {s : ℕ}
    (mask : Fin s → Finset (Fin s))
    (hCover : ∀ j : Fin s, ∃ i : Fin s,
      mask i = (Finset.univ : Finset (Fin s)).erase j) :
    ∃ p : Equiv.Perm (Fin s),
      ∀ j : Fin s, mask (p j) =
        (Finset.univ : Finset (Fin s)).erase j := by
  classical
  let f : Fin s → Fin s := fun j => (hCover j).choose
  have hf (j : Fin s) :
      mask (f j) = (Finset.univ : Finset (Fin s)).erase j :=
    (hCover j).choose_spec
  have hInj : Function.Injective f := by
    intro i j hij
    have hMasks := congrArg mask hij
    rw [hf i, hf j] at hMasks
    have hSingleton :
        ({i} : Finset (Fin s)) = {j} := by
      have hc := congrArg
        (fun S : Finset (Fin s) => Sᶜ) hMasks
      simpa using hc
    have hi : i ∈ ({j} : Finset (Fin s)) := by
      rw [← hSingleton]
      simp
    simpa using hi
  have hBij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hInj, by simp⟩
  exact ⟨Equiv.ofBijective f hBij, hf⟩

/-- Four possible forms of the full-coordinate mask family when
every same-sized mask is represented and there are only s slots. -/
theorem full_mask_family_four_normal_forms {s r : ℕ}
    (mask : Fin s → Finset (Fin s))
    (hs : 0 < s)
    (hCard : ∀ i : Fin s, (mask i).card = r)
    (hCover : ∀ R : Finset (Fin s), R.card = r →
      ∃ i : Fin s, mask i = R)
    (hBound : Nat.choose s r ≤ s) :
    (r = 0 ∧ ∀ i : Fin s, mask i = ∅) ∨
    (r = 1 ∧ ∃ p : Equiv.Perm (Fin s),
      ∀ i : Fin s, mask (p i) = {i}) ∨
    (r + 1 = s ∧ ∃ p : Equiv.Perm (Fin s),
      ∀ i : Fin s, mask (p i) =
        (Finset.univ : Finset (Fin s)).erase i) ∨
    (r = s ∧ ∀ i : Fin s,
      mask i = (Finset.univ : Finset (Fin s))) := by
  classical
  let i0 : Fin s := ⟨0, hs⟩
  have hrs : r ≤ s := by
    rw [← hCard i0]
    exact Finset.card_le_univ _
  obtain hZero | hOne | hPrev | hAll :=
    choose_le_row_index_extreme s r hrs hBound
  · left
    refine ⟨hZero, ?_⟩
    intro i
    exact Finset.card_eq_zero.mp ((hCard i).trans hZero)
  · right; left
    refine ⟨hOne, ?_⟩
    apply singleton_mask_family_reindex mask
    intro j
    apply hCover {j}
    simp [hOne]
  · right; right; left
    refine ⟨hPrev, ?_⟩
    apply cosingleton_mask_family_reindex mask
    intro j
    apply hCover ((Finset.univ : Finset (Fin s)).erase j)
    have hCount :
        ((Finset.univ : Finset (Fin s)).erase j).card = s - 1 := by
      simp
    omega
  · right; right; right
    refine ⟨hAll, ?_⟩
    intro i
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hCard i, hAll]
    simp

end EPPAIII.CliqueCovers
