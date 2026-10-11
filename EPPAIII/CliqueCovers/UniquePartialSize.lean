import EPPAIII.CliqueCovers.InnerRigidity
import EPPAIII.CliqueCovers.Claim39OrbitBridge

/-!
# EPPA saturation: a unique partial size cannot coexist with another

For a double-sized EPPA witness for sK_t, suppose an outside
neighbourhood profile has precisely one coordinate of a fixed proper
size k. The unrestricted Claim 3.9 theorem implies k=1 or t-1.
Its size-k wreath orbit therefore has at least s*t points, the entire
outside-vertex budget. The inner-rigidity theorem then shows that all
other coordinates are empty or full.

This argument is independent of any partition of H \ G and of the
two-sided regularity in the original Claim 3.8.
-/

namespace EPPAIII.CliqueCovers

/-- Under genuine EPPA and the double-size hypothesis,
a unique coordinate of a proper size k forces all other
coordinate sizes to be 0 or t. -/
theorem eppa_unique_partial_size_other_coordinates_trivial {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (k : ℕ) (hs : 0 < s)
    (hk : 0 < k) (hkt : k < t)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) k).card = 1)
    (j : Fin s)
    (hj : j ∉ kPositions (finiteNeighbourhoodProfile H e w) k) :
    (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
      (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t := by
  classical
  let P : Finset (Fin s × Fin t) :=
    finiteNeighbourhoodProfile H e w
  have hOutside : (finiteOutside e).card = s * t :=
    finiteOutside_card_clique_union e hOrder
  have hPartial :
      0 < (kPositions P k).card := by
    change 0 < (kPositions (finiteNeighbourhoodProfile H e w) k).card
    rw [hUnique]
    decide
  have hExtreme : k = 1 ∨ k + 1 = t :=
    eppa_clique_partial_degree_extreme H e heppa
      w hw k hs hk hkt hPartial (le_of_eq hOutside)
  have hChoose : Nat.choose t k = t := by
    rcases hExtreme with hOne | hCo
    · simpa [hOne] using (Nat.choose_one_right t)
    · have hComp : t - k = 1 := by omega
      calc
        Nat.choose t k =
          Nat.choose t (t - k) :=
            (Nat.choose_symm (Nat.le_of_lt hkt)).symm
        _ = Nat.choose t 1 := by rw [hComp]
        _ = t := Nat.choose_one_right t
  have hSaturation :
      Nat.choose s 1 * (Nat.choose t k)^1 = s * t := by
    simp [hChoose]
  have hOrbit :
      (wreathOrbit P).card ≤ Nat.choose s 1 * (Nat.choose t k)^1 := by
    calc
      (wreathOrbit P).card ≤
          (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
        Finset.card_le_card
          (wreathOrbit_subset_finiteProfileOrbit H e w)
      _ ≤ (finiteOutside e).card :=
        finite_profile_orbit_card_le_outside
          (cliqueUnion s t) H e heppa w hw
      _ = s * t := hOutside
      _ = Nat.choose s 1 * (Nat.choose t k)^1 := hSaturation.symm
  exact saturated_profile_other_coordinate_not_partial P 1 k
    hUnique hOrbit j hj

end EPPAIII.CliqueCovers
