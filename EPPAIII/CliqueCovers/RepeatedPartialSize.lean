import EPPAIII.CliqueCovers.Claim39OrbitBridge
import EPPAIII.CliqueCovers.MultiplePartialArithmetic

/-!
# Two proper neighbourhood coordinates of the same size

This theorem combines only previously axiom-audited inputs:
* unrestricted wreath-product profile orbit lower bound,
* EPPA upper bound on the actual profile orbit,
* exact outside half cardinality for a double-sized witness,
* the arithmetic obstruction to multiple partial coordinates.

If the profile of an outside vertex has at least two coordinates of
the same proper nonzero size k, the only possibility is the small
(s,t,k,r)=(2,2,1,2) exception. No hypothesis about a partition or
regularity of the outside vertices is needed.

The *mixed-size* case of two distinct proper degrees is separate,
handled on paper via the saturated orbit-injectivity argument.
-/

namespace EPPAIII.CliqueCovers

theorem repeated_partial_coordinate_exception {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (k r : ℕ)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hk : 0 < k) (hkt : k < t)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hr : 2 ≤ r) :
    s = 2 ∧ t = 2 ∧ r = 2 ∧ k = 1 := by
  classical
  have hrs : r ≤ s := by
    have hCard :
        (kPositions (finiteNeighbourhoodProfile H e w) k).card ≤
          (Finset.univ : Finset (Fin s)).card :=
      Finset.card_le_univ _
    simpa [hR] using hCard
  have hCoeff : t ≤ Nat.choose t k :=
    choose_ge_self t k hk hkt
  have hPow : t ^ r ≤ (Nat.choose t k) ^ r :=
    Nat.pow_le_pow_right hCoeff r
  have hOrbit :
      Nat.choose s r * (Nat.choose t k) ^ r ≤
        (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
    actual_profile_orbit_lower_bound H e w r k hR
  have hOutside :
      (finiteProfileOrbit (cliqueUnion s t) H e w).card ≤ s * t := by
    calc
      (finiteProfileOrbit (cliqueUnion s t) H e w).card ≤
        (finiteOutside e).card :=
        finite_profile_orbit_card_le_outside
          (cliqueUnion s t) H e heppa w hw
      _ = s * t := finiteOutside_card_clique_union e hOrder
  have hBound : Nat.choose s r * t ^ r ≤ s * t := by
    calc
      Nat.choose s r * t ^ r ≤
          Nat.choose s r * (Nat.choose t k) ^ r :=
        Nat.mul_le_mul_left _ hPow
      _ ≤ (finiteProfileOrbit (cliqueUnion s t) H e w).card :=
        hOrbit
      _ ≤ s * t := hOutside
  obtain ⟨hs2,ht2,hr2⟩ :=
    multiple_partial_orbit_arithmetic s t r hs ht hr hrs hBound
  refine ⟨hs2,ht2,hr2,?_⟩
  omega

end EPPAIII.CliqueCovers
