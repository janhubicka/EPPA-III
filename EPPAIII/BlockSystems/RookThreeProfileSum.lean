import EPPAIII.BlockSystems.OutsideProfileMultiplicity
import EPPAIII.BlockSystems.Claim314CrossEdges

/-!
# Fixed-degree outside neighbourhood profiles and the nine-vertex budget

A fixed cross-degree k means every outside vertex has a finite
neighbourhood profile of size k. Summing its profile multiplicity
over all k-subsets therefore counts the complementary half exactly.

For an arbitrary 18-vertex host of an induced nine-vertex rook
graph the outside budget is nine. Combining this with EPPA's
profile multiplicity invariance gives the precise input required
by the finite subgroup orbit arithmetic in Lemma 3.20.

No outside-clique partition or coherent system of extensions
is assumed.
-/

namespace EPPAIII.BlockSystems

/-- All the outside profile multiplicities of fixed size k
add up to the actual number of outside vertices. -/
theorem outside_profile_fixed_size_sum
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W) (k : ℕ)
    (hSize : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = k) :
    (∑ S ∈ (Finset.univ : Finset V).powersetCard k,
      outsideProfileMultiplicity H e S) =
        (finiteOutside e).card := by
  classical
  have hMaps :
      (finiteOutside e : Set W).MapsTo
        (finiteNeighbourhoodProfile H e)
        ((Finset.univ : Finset V).powersetCard k :
          Set (Finset V)) := by
    intro w hw
    exact (Finset.mem_powersetCard).mpr
      ⟨Finset.subset_univ _,hSize w hw⟩
  have hFibres (S : Finset V) :
      outsideProfileMultiplicity H e S =
        ((finiteOutside e).filter
          (fun w => finiteNeighbourhoodProfile H e w = S)).card := by
    unfold outsideProfileMultiplicity
    congr 1
    ext w
    simp
  calc
    (∑ S ∈ (Finset.univ : Finset V).powersetCard k,
        outsideProfileMultiplicity H e S) =
      ∑ S ∈ (Finset.univ : Finset V).powersetCard k,
        ((finiteOutside e).filter
          (fun w => finiteNeighbourhoodProfile H e w = S)).card := by
            apply Finset.sum_congr rfl
            intro S _
            exact hFibres S
    _ = (finiteOutside e).card :=
      (Finset.card_eq_sum_card_fiberwise
        (s := finiteOutside e)
        (t := (Finset.univ : Finset V).powersetCard k)
        (f := finiteNeighbourhoodProfile H e) hMaps).symm

/-- The complementary half of an 18-vertex host containing
an induced nine-vertex rook graph has exactly nine points. -/
theorem rook_outside_card_nine
    {W : Type*} [Fintype W]
    (e : (Fin 3 × Fin 3) ↪ W)
    (h18 : Fintype.card W = 18) :
    (finiteOutside e).card = 9 := by
  have hBase : Fintype.card (Fin 3 × Fin 3) = 9 := by
    decide
  have hSize := finiteOutside_card e
  omega

/-- One EPPA lift per base automorphism gives the exact
weight-invariance hypothesis used in the rook orbit sums. -/
theorem rook_profile_weight_invariance
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e) :
    ∀ S : Finset (Fin 3 × Fin 3), ∀ p : rookAutParameter,
      outsideProfileMultiplicity H e
        (S.image (rookParameterizedAut p)) =
          outsideProfileMultiplicity H e S := by
  intro S p
  exact (rook_outside_profile_multiplicity_invariant
    H e heppa S p).symm

/-- For an R3 witness of order 18, a uniform cross-degree k
forces invariant profile weights of total nine on k-subsets. -/
theorem rook_profile_total_nine
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (h18 : Fintype.card W = 18)
    (k : ℕ)
    (hSize : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = k) :
    (∑ S ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).powersetCard k,
      outsideProfileMultiplicity H e S) = 9 := by
  rw [outside_profile_fixed_size_sum H e k hSize,
    rook_outside_card_nine e h18]

end EPPAIII.BlockSystems
