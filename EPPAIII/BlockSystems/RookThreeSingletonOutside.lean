import EPPAIII.BlockSystems.OutsideOrbitSaturation
import EPPAIII.BlockSystems.RookThreeOutsideEquiv
import EPPAIII.BlockSystems.RookThreeOutsideAction
import EPPAIII.BlockSystems.RookThreeOutsideEqualEdges

/-!
# The actual outside matching profiles in the R3 exception

One outside singleton neighbourhood in an eighteen-vertex EPPA
host of the nine-vertex rook graph forces all nine singleton
profiles to occur exactly once. This follows from the nine
genuine row/column translations and the outside-vertex budget,
without an assumed action on the outside half or any coherent
choice of EPPA lifts.

Under the resulting canonical outside labels, all 72 rook
automorphisms act as genuine outside automorphisms.
Vertex transitivity forces equal internal edge counts, so
the outside graph is the rook graph or its complement.
This is the cross-degree-one branch of Lemma 3.20.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- All nine singleton subsets form one orbit under the nine
genuine row/column translations of the rook graph. -/
theorem rook_singleton_translation_orbit_eq_labels :
    ∀ a : rookVertex,
      ((Finset.univ : Finset rookVertex).image
        (fun d => ({a} : Finset rookVertex).image
          (rookThreeTranslation d))) =
      (Finset.univ : Finset rookVertex).image
        (fun x => ({x} : Finset rookVertex)) := by
  decide

theorem rook_singleton_translation_orbit_card :
    ∀ a : rookVertex,
      (((Finset.univ : Finset rookVertex).image
        (fun d => ({a} : Finset rookVertex).image
          (rookThreeTranslation d))).card) = 9 := by
  decide

/-- An actual singleton outside neighbourhood saturates every
outside vertex and yields a unique full set of singleton profiles. -/
theorem rook_eppa_one_singleton_profile_saturates
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
      (Finset.univ : Finset rookVertex).image
        (fun x => ({x} : Finset rookVertex)) ∧
      Set.InjOn (finiteNeighbourhoodProfile H e)
        (finiteOutside e : Set W) := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hOne
  have hBudget :
      (((Finset.univ : Finset rookVertex).image
        (fun d => (finiteNeighbourhoodProfile H e w).image
          (rookThreeTranslation d))).card) =
        (finiteOutside e).card := by
    rw [ha, rook_singleton_translation_orbit_card a,
      rook_outside_card_nine e h18]
  obtain ⟨hImage,hInj⟩ :=
    eppa_outside_orbit_saturation_of_card
      rookThreeGraph H e heppa
      rookThreeTranslation rookThree_translation_graph_automorphism
      w hw hBudget
  have hImage' :
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        (Finset.univ : Finset rookVertex).image
          (fun x => ({x} : Finset rookVertex)) := by
    calc
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          (Finset.univ : Finset rookVertex).image
            (fun d => (finiteNeighbourhoodProfile H e w).image
              (rookThreeTranslation d)) := hImage
      _ = _ := by rw [ha,rook_singleton_translation_orbit_eq_labels a]
  exact ⟨hImage',hInj⟩

/-- The outside half is canonically indexed by the unique
selected neighbour of each outside vertex. -/
theorem rook_eppa_singleton_outside_equiv
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ f : rookVertex ≃ {v : W // v ∈ finiteOutside e},
      ∀ x : rookVertex,
        finiteNeighbourhoodProfile H e (f x).val = {x} := by
  classical
  obtain ⟨hImage,hInj⟩ :=
    rook_eppa_one_singleton_profile_saturates
      H e heppa h18 w hw hOne
  have hLabelInj : Function.Injective
      (fun x : rookVertex => ({x} : Finset rookVertex)) := by
    intro x y hxy
    have hx : x ∈ ({y} : Finset rookVertex) := by
      rw [← hxy]
      simp
    simpa using hx
  exact outside_profile_label_family_equiv
    H e (fun x => ({x} : Finset rookVertex))
    hLabelInj hImage hInj

/-- Actual EPPA lifts of the indexed rook automorphisms act
on singleton-labelled outside vertices under the same
rook permutation. -/
theorem rook_eppa_singleton_outside_graph_invariant
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (f : rookVertex ≃ {v : W // v ∈ finiteOutside e})
    (hLabels : ∀ x : rookVertex,
      finiteNeighbourhoodProfile H e (f x).val = {x})
    (hInj : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W)) :
    ∀ p : rookAutParameter,
      IsGraphAutomorphism (H.comap (fun x => (f x).val))
        (rookParameterizedAut p) := by
  intro p
  exact canonical_outside_graph_automorphism
    rookThreeGraph H e heppa
    (rookParameterizedAut p)
    (rookParameterizedAut_graph_automorphism p)
    (fun x => ({x} : Finset rookVertex))
    (fun x => (f x).val)
    (fun x => (f x).property)
    hLabels hInj (by intro x; simp)

/-- R3 cross-degree one: the selected singleton matching
labels the outside graph, which must be R3 or its complement.
No preliminary outside block decomposition or action is assumed. -/
theorem rook_eppa_singleton_outside_graph_two_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (h18 : Fintype.card W = 18)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ f : rookVertex ≃ {v : W // v ∈ finiteOutside e},
      (∀ x : rookVertex,
        finiteNeighbourhoodProfile H e (f x).val = {x}) ∧
      (H.comap (fun x => (f x).val) = rookThreeGraph ∨
       H.comap (fun x => (f x).val) = rookThreeGraphᶜ) := by
  classical
  obtain ⟨f,hLabels⟩ :=
    rook_eppa_singleton_outside_equiv H e heppa h18 w hw hOne
  have hInj : Set.InjOn
      (finiteNeighbourhoodProfile H e) (finiteOutside e : Set W) :=
    (rook_eppa_one_singleton_profile_saturates
      H e heppa h18 w hw hOne).2
  let outside : rookVertex → W := fun x => (f x).val
  have hFour :
      H.comap outside = ⊥ ∨
      H.comap outside = rookThreeGraph ∨
      H.comap outside = rookThreeGraphᶜ ∨
      H.comap outside = ⊤ :=
    rook_invariant_graph_four_forms (H.comap outside)
      (rook_eppa_singleton_outside_graph_invariant
        H e heppa f hLabels hInj)
  have hSide :
      ((CliqueCovers.outsideInducedGraph H e).comap f).edgeSet.ncard =
        rookThreeGraph.edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      rookThreeGraph H e heppa.1 f hTrans
  have hSideGraph :
      ((CliqueCovers.outsideInducedGraph H e).comap f =
        H.comap outside) := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hCount : (H.comap outside).edgeSet.ncard = 18 := by
    rw [hSideGraph,rookThreeGraph_edge_count_eighteen] at hSide
    exact hSide
  rcases hFour with hEmpty | hRook | hComplement | hFull
  · have hZero : (H.comap outside).edgeSet.ncard = 0 := by
      rw [hEmpty]
      simp
    omega
  · exact ⟨f,hLabels,Or.inl hRook⟩
  · exact ⟨f,hLabels,Or.inr hComplement⟩
  · have hThirtySix : (H.comap outside).edgeSet.ncard = 36 := by
      rw [hFull]
      exact rookNineComplete_edge_count_thirtysix
    omega

end EPPAIII.BlockSystems
