import EPPAIII.BlockSystems.CycleFiveProperProfileSaturation
import EPPAIII.BlockSystems.RookThreeOutsideEquiv
import EPPAIII.BlockSystems.OutsideProfileCanonicalAction
import EPPAIII.BlockSystems.CycleFiveInvariantFourForms
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.BlockSystems.CycleFiveOutsideAction

/-!
# Actual C5 outside graph from an arbitrary proper neighbourhood profile

For a ten-vertex vertex-transitive EPPA witness of the induced
five-cycle, a single nonempty proper outside neighbourhood profile
already labels all five outside vertices by its cyclic shifts.

The genuine EPPA lifts of rotations act by the same shifts on
these canonical labels. The outside graph is consequently
rotation-invariant and therefore one of four explicit forms.
Equal internal edge counts eliminate the empty and complete
forms, leaving C5 or its complement (both abstract five-cycles).

No imprimitive block system, outside transitivity, uniform
cross-degree, or coherent EPPA extensions are assumed.
The all-empty/full-profile case remains separate.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

/-- Any nonempty proper profile has five distinct cyclic shifts,
hence gives an injective labelling by the rotation parameter. -/
theorem cycleFive_proper_shift_injective
    (S : Finset (Fin 5))
    (hNe : S ≠ ∅)
    (hFull : S ≠ (Finset.univ : Finset (Fin 5))) :
    Function.Injective
      (fun d : Fin 5 => S.image (Equiv.addRight d)) := by
  classical
  have hOrbit := cycleFive_proper_subset_orbit_size S hNe hFull
  have hCard :
      ((Finset.univ : Finset (Fin 5)).image
        (fun d => S.image (Equiv.addRight d))).card =
      (Finset.univ : Finset (Fin 5)).card := by
    change (cycleFiveSubsetOrbit S).card =
      (Finset.univ : Finset (Fin 5)).card
    rw [hOrbit]
    decide
  have hInjOn := Finset.injOn_of_card_image_eq hCard
  intro x y hxy
  exact hInjOn (Finset.mem_univ x) (Finset.mem_univ y) hxy

/-- Rotation of a translated profile agrees with translating
by the sum of the two rotations. -/
theorem cycleFive_shift_profile_equivariant
    (S : Finset (Fin 5)) (x d : Fin 5) :
    S.image (Equiv.addRight (x + d)) =
      (S.image (Equiv.addRight x)).image (Equiv.addRight d) := by
  classical
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨v,hv,hvy⟩
    refine ⟨v + x, ⟨v,hv,rfl⟩, ?_⟩
    change (v + x) + d = y
    calc
      (v + x) + d = v + (x + d) := by abel
      _ = y := hvy
  · rintro ⟨u,⟨v,hv,hvu⟩,huy⟩
    refine ⟨v,hv,?_⟩
    change v + (x + d) = y
    calc
      v + (x + d) = (v + x) + d := by abel
      _ = u + d := congrArg (· + d) hvu
      _ = y := huy

/-- Canonical outside coordinates are a conclusion of EPPA
and the saturation of any one proper profile. -/
theorem cycleFive_eppa_proper_profile_outside_equiv
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hNe : finiteNeighbourhoodProfile H e w ≠ ∅)
    (hFull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5))) :
    ∃ f : (Fin 5) ≃ {u : W // u ∈ finiteOutside e},
      ∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          (finiteNeighbourhoodProfile H e w).image
            (Equiv.addRight x) := by
  classical
  let S : Finset (Fin 5) := finiteNeighbourhoodProfile H e w
  obtain ⟨hImage,hInjective⟩ :=
    cycleFive_eppa_proper_profile_saturates_outside
      H e heppa hTen w hw hNe hFull
  have hImageShift :
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        (Finset.univ : Finset (Fin 5)).image
          (fun x => S.image (Equiv.addRight x)) := by
    calc
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          cycleFiveSubsetOrbit S := hImage
      _ = _ := rfl
  exact outside_profile_label_family_equiv H e
    (fun x => S.image (Equiv.addRight x))
    (cycleFive_proper_shift_injective S hNe hFull)
    hImageShift hInjective

/-- Uniquely labelled outside profiles transport actual EPPA
rotations to actual outside automorphisms. -/
theorem cycleFive_proper_outside_graph_rotations
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (S : Finset (Fin 5))
    (outside : Fin 5 → W)
    (hOutside : ∀ x : Fin 5, outside x ∈ finiteOutside e)
    (hLabels : ∀ x : Fin 5,
      finiteNeighbourhoodProfile H e (outside x) =
        S.image (Equiv.addRight x))
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W)) :
    ∀ d : Fin 5,
      IsGraphAutomorphism (H.comap outside) (Equiv.addRight d) := by
  intro d
  exact canonical_outside_graph_automorphism
    (SimpleGraph.cycleGraph 5) H e heppa
    (Equiv.addRight d) (cycleFive_translate_graph_automorphism d)
    (fun x => S.image (Equiv.addRight x))
    outside hOutside hLabels hInjective
    (fun x => cycleFive_shift_profile_equivariant S x d)

/-- Rotation-invariant five-vertex graphs with five edges are
exactly C5 and its complement. -/
theorem cycleFive_invariant_five_edges_two_forms
    (K : SimpleGraph (Fin 5))
    (hRot : ∀ d : Fin 5,
      IsGraphAutomorphism K (Equiv.addRight d))
    (hEdges : K.edgeSet.ncard = 5) :
    K = SimpleGraph.cycleGraph 5 ∨
      K = (SimpleGraph.cycleGraph 5)ᶜ := by
  classical
  rcases cycleFive_invariant_graph_four_forms K hRot with
    hEmpty | hCycle | hComplement | hComplete
  · have hZero : K.edgeSet.ncard = 0 := by
      rw [hEmpty]
      simp
    omega
  · exact Or.inl hCycle
  · exact Or.inr hComplement
  · have hTen : K.edgeSet.ncard = 10 := by
      rw [hComplete]
      exact cycleFive_complete_edge_count_ten
    omega

/-- The actual complementary graph of any order-ten transitive
EPPA host with at least one proper selected-neighbourhood
profile is a five-cycle in canonical cyclic coordinates,
or the complementary five-cycle. No outside block action is
assumed and the proper cross-degree need not be specified. -/
theorem cycleFive_eppa_proper_outside_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hNe : finiteNeighbourhoodProfile H e w ≠ ∅)
    (hFull : finiteNeighbourhoodProfile H e w ≠
      (Finset.univ : Finset (Fin 5))) :
    ∃ f : Fin 5 ≃ {u : W // u ∈ finiteOutside e},
      (∀ x : Fin 5,
        finiteNeighbourhoodProfile H e (f x).val =
          (finiteNeighbourhoodProfile H e w).image
            (Equiv.addRight x)) ∧
      (H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
        H.comap (fun x => (f x).val) =
          (SimpleGraph.cycleGraph 5)ᶜ) := by
  classical
  obtain ⟨f,hLabels⟩ := cycleFive_eppa_proper_profile_outside_equiv
    H e heppa hTen w hw hNe hFull
  have hInj : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W) :=
    (cycleFive_eppa_proper_profile_saturates_outside
      H e heppa hTen w hw hNe hFull).2
  let outside : Fin 5 → W := fun x => (f x).val
  have hOut : ∀ x : Fin 5, outside x ∈ finiteOutside e := fun x => (f x).property
  have hRot : ∀ d : Fin 5, IsGraphAutomorphism
      (H.comap outside) (Equiv.addRight d) :=
    cycleFive_proper_outside_graph_rotations
      H e heppa (finiteNeighbourhoodProfile H e w)
      outside hOut hLabels hInj
  have hSide :
      ((CliqueCovers.outsideInducedGraph H e).comap f).edgeSet.ncard =
        (SimpleGraph.cycleGraph 5).edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      (SimpleGraph.cycleGraph 5) H e heppa.1 f hTrans
  have hSideGraph :
      ((CliqueCovers.outsideInducedGraph H e).comap f) =
        H.comap outside := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hFive : (H.comap outside).edgeSet.ncard = 5 := by
    rw [hSideGraph,cycleFive_edge_count_five] at hSide
    exact hSide
  exact ⟨f,hLabels,cycleFive_invariant_five_edges_two_forms
    (H.comap outside) hRot hFive⟩

end EPPAIII.BlockSystems
