import EPPAIII.BlockSystems.RookThreeProfileSum
import EPPAIII.BlockSystems.RookThreeFourOrbitWeights

/-!
# EPPA orbit obstructions for the exceptional nine-vertex R3

We now compose the actual EPPA outside-profile multiplicities
with the verified finite subset orbit arithmetic.

For an 18-vertex EPPA host of the induced R3, if every
complementary vertex has exactly k selected neighbours,
then k cannot be 2 or 3. If k=4, exactly one of the two
size-nine orbit types (base open neighbourhoods or strict
nonneighbourhoods) occurs with multiplicity one, and
all other four-subset types occur with multiplicity zero.

The proofs do not assume coherence of EPPA extensions,
an outside clique partition, or a particular action on
outside vertices. Uniform cross-degree is an explicit
hypothesis; deriving it from host regularity and the
other half's structure belongs to Lemma 3.20's
remaining graph-classification assembly.
-/

namespace EPPAIII.BlockSystems

/-- The outside cross-degree cannot be two. -/
theorem rook_eppa_outside_cross_degree_two_impossible
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 2) :
    False :=
  rook_pair_weight_total_ne_nine
    (outsideProfileMultiplicity H e)
    (rook_profile_weight_invariance H e heppa)
    (rook_profile_total_nine H e h18 2 hDegree)

/-- The outside cross-degree cannot be three. The obstruction
uses multiplicities, not only the bound 6 ≤ 9 on one orbit. -/
theorem rook_eppa_outside_cross_degree_three_impossible
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 3) :
    False :=
  rook_triple_weight_total_ne_nine
    (outsideProfileMultiplicity H e)
    (rook_profile_weight_invariance H e heppa)
    (rook_profile_total_nine H e h18 3 hDegree)

/-- With outside cross-degree four, every outside vertex
belongs to precisely one of the two nine-element profile
orbits, with each orbit profile represented once.
Equivalently, the two nine-orbit representative
multiplicities sum to one and all other four-orbit
representatives occur zero times. -/
theorem rook_eppa_outside_cross_degree_four_profile_classification
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 4) :
    outsideProfileMultiplicity H e rookFourSquare +
      outsideProfileMultiplicity H e rookFourNineOther = 1 ∧
    outsideProfileMultiplicity H e rookFourLinePlus = 0 ∧
    outsideProfileMultiplicity H e rookFourCornerPlus = 0 ∧
    outsideProfileMultiplicity H e rookFourCornerDiagonal = 0 :=
  rook_four_weight_total_nine_classification
    (outsideProfileMultiplicity H e)
    (rook_profile_weight_invariance H e heppa)
    (rook_profile_total_nine H e h18 4 hDegree)

end EPPAIII.BlockSystems
