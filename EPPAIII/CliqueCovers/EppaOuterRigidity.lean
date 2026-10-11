import EPPAIII.CliqueCovers.OuterRigidity
import EPPAIII.CliqueCovers.UniquePartialSize

/-!
# EPPA-level rigidity of the unselected neighbourhood slices

The outer-rigidity lemma is combinatorial. This file transfers it to
the genuine finite EPPA orbit of an outside vertex of a host of order
2*s*t, in the same way as the verified Claim 3.9 bridge.

When exactly one proper coordinate size k occurs, the existing
extreme-degree theorem gives choose(t,k)=t, so its choice-space
count is exactly s*t. Thus all other coordinate slices are identical.
The earlier unique-partial theorem says they are each empty or full,
which now makes their empty/full status uniform.

No stabilizer of a complementary D_j is used.
-/

namespace EPPAIII.CliqueCovers

/-- EPPA transfers saturation of size-k choices into equality
of all unselected whole neighbourhood slices. -/
theorem eppa_saturated_other_slices_equal {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (i j : Fin s)
    (hi : i ∉ kPositions (finiteNeighbourhoodProfile H e w) k)
    (hj : j ∉ kPositions (finiteNeighbourhoodProfile H e w) k) :
    profileSlice (finiteNeighbourhoodProfile H e w) i =
      profileSlice (finiteNeighbourhoodProfile H e w) j := by
  classical
  have hBound :
      (wreathOrbit (finiteNeighbourhoodProfile H e w)).card ≤
        Nat.choose s r * (Nat.choose t k)^r := by
    calc
      (wreathOrbit (finiteNeighbourhoodProfile H e w)).card ≤
          (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
        Finset.card_le_card (wreathOrbit_subset_finiteProfileOrbit H e w)
      _ ≤ (finiteOutside e).card :=
        finite_profile_orbit_card_le_outside
          (cliqueUnion s t) H e heppa w hw
      _ = s * t := finiteOutside_card_clique_union e hOrder
      _ = Nat.choose s r * (Nat.choose t k)^r := hSat.symm
  exact saturated_profile_other_slices_equal
    (finiteNeighbourhoodProfile H e w) r k hR hBound i j hi hj

/-- In a double-sized EPPA host, if a proper size k occurs at
exactly one clique, all other clique-neighbourhood slices coincide.
Combined with UniquePartialSize, those slices are uniformly
empty or uniformly full. -/
theorem eppa_unique_partial_other_slices_equal {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (k : ℕ) (hs : 0 < s)
    (hk : 0 < k) (hkt : k < t)
    (hUnique : (kPositions (finiteNeighbourhoodProfile H e w) k).card = 1)
    (i j : Fin s)
    (hi : i ∉ kPositions (finiteNeighbourhoodProfile H e w) k)
    (hj : j ∉ kPositions (finiteNeighbourhoodProfile H e w) k) :
    profileSlice (finiteNeighbourhoodProfile H e w) i =
      profileSlice (finiteNeighbourhoodProfile H e w) j := by
  classical
  have hPartial :
      0 < (kPositions (finiteNeighbourhoodProfile H e w) k).card := by
    rw [hUnique]
    decide
  have hExtreme : k = 1 ∨ k + 1 = t :=
    eppa_clique_partial_degree_extreme H e heppa
      w hw k hs hk hkt hPartial
      (le_of_eq (finiteOutside_card_clique_union e hOrder))
  have hChoose : Nat.choose t k = t := by
    rcases hExtreme with hOne | hCo
    · simpa [hOne] using (Nat.choose_one_right t)
    · have hComp : t - k = 1 := by omega
      calc
        Nat.choose t k = Nat.choose t (t - k) :=
          (Nat.choose_symm (Nat.le_of_lt hkt)).symm
        _ = Nat.choose t 1 := by rw [hComp]
        _ = t := Nat.choose_one_right t
  have hSat : Nat.choose s 1 * (Nat.choose t k)^1 = s * t := by
    simp [hChoose]
  exact eppa_saturated_other_slices_equal
    H e heppa hOrder w hw 1 k hUnique hSat i j hi hj

end EPPAIII.CliqueCovers
