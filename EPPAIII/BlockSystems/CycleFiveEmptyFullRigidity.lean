import EPPAIII.BlockSystems.CycleFiveProperOutsideAction
import EPPAIII.EPPA.OutsideCardinality

/-!
# The empty/full outside neighbourhood case for the five-cycle

For an induced five-cycle in a ten-vertex vertex-transitive host,
the complementary half contains exactly five vertices. If one of
these sees all five selected vertices, its total degree is at least
five; if another sees none, its degree is at most four (it has only
four possible distinct neighbours in the complementary half).
Regularity therefore forbids these two profile types from coexisting.

This handles the missing first step of the all-empty/full case of
Lemma 3.18 without EPPA. It does not yet assert that the outside
induced graph is a five-cycle: that requires a separate component
or five-vertex 2-regular classification.
-/

namespace EPPAIII.BlockSystems

/-- In an order-ten host with a distinguished embedded five-set,
there are exactly five outside vertices. -/
theorem cycleFive_outside_card_five
    {W : Type*} [Fintype W]
    (e : (Fin 5) ↪ W)
    (hTen : Fintype.card W = 10) :
    (finiteOutside e).card = 5 := by
  have h := finiteOutside_card e
  have hBase : Fintype.card (Fin 5) = 5 := by decide
  omega

/-- An outside vertex adjacent to all five selected vertices
has total degree at least five. -/
theorem cycleFive_full_profile_degree_ge_five
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W) (w : W)
    (hFull : finiteNeighbourhoodProfile H e w =
      (Finset.univ : Finset (Fin 5))) :
    5 ≤ H.degree w := by
  classical
  let S : Finset W := (Finset.univ : Finset (Fin 5)).image e
  have hCard : S.card = 5 := by
    calc
      S.card = (Finset.univ : Finset (Fin 5)).card :=
        Finset.card_image_of_injective _ e.injective
      _ = 5 := by decide
  have hSubset : S ⊆ H.neighborFinset w := by
    intro v hv
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
    have hx : x ∈ finiteNeighbourhoodProfile H e w := by
      rw [hFull]
      exact Finset.mem_univ x
    have hAdj : H.Adj w (e x) := by
      simpa only [finiteNeighbourhoodProfile,
        Finset.mem_filter, Finset.mem_univ, true_and] using hx
    exact (H.mem_neighborFinset w (e x)).mpr hAdj
  have hLE : S.card ≤ (H.neighborFinset w).card :=
    Finset.card_le_card hSubset
  simpa only [hCard, SimpleGraph.degree] using hLE

/-- An outside vertex adjacent to no selected vertices has total
degree at most four, since there are only five outside vertices
and the graph has no loops. -/
theorem cycleFive_empty_profile_degree_le_four
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W) (w : W)
    (hw : w ∈ finiteOutside e)
    (hTen : Fintype.card W = 10)
    (hEmpty : finiteNeighbourhoodProfile H e w = ∅) :
    H.degree w ≤ 4 := by
  classical
  have hOutsideCard := cycleFive_outside_card_five e hTen
  have hSubset : H.neighborFinset w ⊆ (finiteOutside e).erase w := by
    intro v hv
    have hAdj : H.Adj w v := (H.mem_neighborFinset w v).mp hv
    have hOutside : v ∈ finiteOutside e := by
      have hNotRange : v ∉ Set.range e := by
        intro hr
        obtain ⟨x,rfl⟩ := hr
        have hx : x ∈ finiteNeighbourhoodProfile H e w := by
          simpa only [finiteNeighbourhoodProfile, Finset.mem_filter,
            Finset.mem_univ, true_and] using hAdj
        rw [hEmpty] at hx
        simpa using hx
      simpa only [finiteOutside, Finset.mem_filter,
        Finset.mem_univ, true_and] using hNotRange
    exact Finset.mem_erase.mpr
      ⟨(H.ne_of_adj hAdj).symm,hOutside⟩
  have hEraseCard : ((finiteOutside e).erase w).card = 4 := by
    rw [Finset.card_erase_of_mem hw, hOutsideCard]
  have hLE := Finset.card_le_card hSubset
  simpa only [SimpleGraph.degree, hEraseCard] using hLE

/-- Two complementary vertices cannot have empty and full
selected neighbourhoods in a regular ten-vertex host. -/
theorem cycleFive_no_mixed_empty_full_profiles
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (hTen : Fintype.card W = 10)
    (d : ℕ) (hReg : H.IsRegularOfDegree d)
    (u v : W) (hv : v ∈ finiteOutside e)
    (hFull : finiteNeighbourhoodProfile H e u =
      (Finset.univ : Finset (Fin 5)))
    (hEmpty : finiteNeighbourhoodProfile H e v = ∅) :
    False := by
  have hu := cycleFive_full_profile_degree_ge_five H e u hFull
  have hvBound :=
    cycleFive_empty_profile_degree_le_four H e v hv hTen hEmpty
  have hU := hReg u
  have hV := hReg v
  omega

/-- If all outside profiles are empty or full, vertex-transitivity
forces them all to be empty, or all to be full. No EPPA, block
system, or outside action is needed for this dichotomy. -/
theorem cycleFive_transitive_empty_full_profiles_uniform
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (hTen : Fintype.card W = 10)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hProfiles : ∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w = ∅ ∨
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))) :
    (∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w = ∅) ∨
    (∀ w : W, w ∈ finiteOutside e →
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))) := by
  classical
  haveI : Nonempty W := ⟨e (0 : Fin 5)⟩
  obtain ⟨d,hReg⟩ := CliqueCovers.regular_of_transitive_graph H hTrans
  by_cases hExistsFull : ∃ w : W, w ∈ finiteOutside e ∧
      finiteNeighbourhoodProfile H e w =
        (Finset.univ : Finset (Fin 5))
  · right
    obtain ⟨u,_,hu⟩ := hExistsFull
    intro v hv
    rcases hProfiles v hv with hEmpty | hFull
    · exact False.elim
        (cycleFive_no_mixed_empty_full_profiles
          H e hTen d hReg u v hv hu hEmpty)
    · exact hFull
  · left
    intro w hw
    rcases hProfiles w hw with hEmpty | hFull
    · exact hEmpty
    · exact False.elim (hExistsFull ⟨w,hw,hFull⟩)

end EPPAIII.BlockSystems
