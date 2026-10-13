import EPPAIII.CliqueCovers.TwoPartialCoordinates

/-!
# Case split by the number of proper partial neighbourhood coordinates

For a double-sized EPPA witness of sK_t, distinguish outside
profile coordinates with size strictly between 0 and t.
The verified two-partial theorem forces s=t=2 if any two distinct
proper partial coordinates exist.

Otherwise there is at most one such coordinate. If exactly one
occurs, it is a singleton or co-singleton and is precisely the
unique coordinate of its fixed partial size k. This is the clean
interface for applying the complete singleton/co-singleton host
theorems, or the exceptional Wagner graph theorem.

No vertex-transitivity, complementary clique partition, or
coherence assumption about EPPA lifts is used in this case split.
-/

namespace EPPAIII.CliqueCovers

/-- Selected clique indices where an outside neighbourhood slice
is neither empty nor the whole K_t. -/
noncomputable def properPartialPositions {s t : ℕ}
    (P : Finset (Fin s × Fin t)) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter
    (fun i => 0 < (profileSlice P i).card ∧
      (profileSlice P i).card < t)

/-- A coordinate is proper precisely when its slice has cardinality
strictly between zero and t. -/
theorem mem_properPartialPositions {s t : ℕ}
    (P : Finset (Fin s × Fin t)) (i : Fin s) :
    i ∈ properPartialPositions P ↔
      0 < (profileSlice P i).card ∧ (profileSlice P i).card < t := by
  classical
  simp [properPartialPositions]

/-- If at least two proper partial coordinates occur in an outside
profile of a double-sized EPPA witness, then s=t=2. -/
theorem eppa_two_proper_partial_positions_exception {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hTwo :
      2 ≤ (properPartialPositions
        (finiteNeighbourhoodProfile H e w)).card) :
    s = 2 ∧ t = 2 := by
  classical
  let P := finiteNeighbourhoodProfile H e w
  let S := properPartialPositions P
  have hPair :
      ∃ i ∈ S, ∃ j ∈ S, i ≠ j :=
    Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨i,hi,j,hj,hij⟩ := hPair
  have hiPartial := (mem_properPartialPositions P i).mp hi
  have hjPartial := (mem_properPartialPositions P j).mp hj
  exact eppa_two_partial_coordinates_exception
    H e heppa hOrder w hw hs ht i j hij
      hiPartial.1 hiPartial.2 hjPartial.1 hjPartial.2

/-- A uniquely proper coordinate is also the unique coordinate
of that particular positive proper cardinality k. -/
theorem unique_proper_partial_gives_unique_k {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (hOne : (properPartialPositions P).card = 1) :
    ∃ (i : Fin s) (k : ℕ),
      0 < k ∧ k < t ∧
      (profileSlice P i).card = k ∧
      (kPositions P k).card = 1 := by
  classical
  obtain ⟨i,hS⟩ :=
    Finset.card_eq_one.mp hOne
  have hi : i ∈ properPartialPositions P := by
    rw [hS]
    simp
  obtain ⟨hkpos,hkproper⟩ :=
    (mem_properPartialPositions P i).mp hi
  let k := (profileSlice P i).card
  have hPosition : kPositions P k = {i} := by
    apply Finset.eq_of_subset_of_card_le
    · intro j hj
      have hjSize : (profileSlice P j).card = k :=
        (mem_kPositions P k j).mp hj
      have hjPartial : j ∈ properPartialPositions P :=
        (mem_properPartialPositions P j).mpr
          ⟨by simpa [k,hjSize] using hkpos,
           by simpa [k,hjSize] using hkproper⟩
      rw [hS] at hjPartial
      exact hjPartial
    · have hiK : i ∈ kPositions P k :=
        (mem_kPositions P k i).mpr rfl
      have hLower : 1 ≤ (kPositions P k).card :=
        Finset.card_pos.mpr ⟨i,hiK⟩
      simpa using hLower
  exact ⟨i,k,hkpos,hkproper,rfl,by rw [hPosition]; simp⟩

/-- As soon as there are two nontrivial cliques, every outside
profile either has no proper partial coordinate, has exactly one,
or belongs to the s=t=2 exceptional parameter case. -/
theorem eppa_proper_partial_trichotomy {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    (properPartialPositions
        (finiteNeighbourhoodProfile H e w)).card = 0 ∨
    (properPartialPositions
        (finiteNeighbourhoodProfile H e w)).card = 1 ∨
    (s = 2 ∧ t = 2) := by
  let n := (properPartialPositions
    (finiteNeighbourhoodProfile H e w)).card
  by_cases hTwo : 2 ≤ n
  · exact Or.inr (Or.inr
      (eppa_two_proper_partial_positions_exception
        H e heppa hOrder w hw hs ht hTwo))
  · have hn : n = 0 ∨ n = 1 := by omega
    exact hn.elim Or.inl (fun h => Or.inr (Or.inl h))

end EPPAIII.CliqueCovers
