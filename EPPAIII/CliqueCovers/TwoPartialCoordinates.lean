import EPPAIII.CliqueCovers.RepeatedPartialSize
import EPPAIII.CliqueCovers.UniquePartialSize

/-!
# Two partial coordinates force the eight-vertex exceptional parameters

This is the graph-level combination of the two independent obstructions:
* if two proper partial coordinates have the same size, the verified
  repeated-size orbit bound forces s=t=2;
* if the first proper size occurs only once, the saturation theorem
  makes every coordinate of another size empty or full.

Thus the only way a double-sized EPPA witness for sK_t can have
two proper nonempty coordinates in one outside profile is s=t=2.
No outside clique partition, vertex-transitivity, or two-sided
D_j regularity is assumed.

The separate identification of the resulting eight-vertex graph as
Wagner, using host vertex-transitivity and the inside/outside edge
count, is not asserted by this theorem.
-/

namespace EPPAIII.CliqueCovers

/-- Distinct partial coordinates are possible only for s=t=2. -/
theorem eppa_two_partial_coordinates_exception {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (i j : Fin s) (hij : i ≠ j)
    (hiPos : 0 < (profileSlice (finiteNeighbourhoodProfile H e w) i).card)
    (hiProper : (profileSlice (finiteNeighbourhoodProfile H e w) i).card < t)
    (hjPos : 0 < (profileSlice (finiteNeighbourhoodProfile H e w) j).card)
    (hjProper : (profileSlice (finiteNeighbourhoodProfile H e w) j).card < t) :
    s = 2 ∧ t = 2 := by
  classical
  let P : Finset (Fin s × Fin t) := finiteNeighbourhoodProfile H e w
  let k : ℕ := (profileSlice P i).card
  let r : ℕ := (kPositions P k).card
  have hik : i ∈ kPositions P k :=
    (mem_kPositions P k i).mpr rfl
  have hrpos : 0 < r :=
    Finset.card_pos.mpr ⟨i, hik⟩
  by_cases hr2 : 2 ≤ r
  · have hR :
        (kPositions (finiteNeighbourhoodProfile H e w) k).card = r := rfl
    obtain ⟨hs2,ht2,_,_⟩ :=
      repeated_partial_coordinate_exception H e heppa hOrder
        w hw k r hs ht hiPos hiProper hR hr2
    exact ⟨hs2,ht2⟩
  · have hr1 : r = 1 := by omega
    have hjNot : j ∉ kPositions P k := by
      intro hj
      have hCard : (kPositions P k).card ≤ 1 := by
        change r ≤ 1
        omega
      have hEq : i = j :=
        (Finset.card_le_one_iff.mp hCard) hik hj
      exact hij hEq
    have hUnique :
        (kPositions (finiteNeighbourhoodProfile H e w) k).card = 1 := by
      simpa only [r, P] using hr1
    have hTrivial :=
      eppa_unique_partial_size_other_coordinates_trivial
        H e heppa hOrder w hw k (by omega)
        hiPos hiProper hUnique j hjNot
    rcases hTrivial with hZero | hFull
    · omega
    · omega

end EPPAIII.CliqueCovers
