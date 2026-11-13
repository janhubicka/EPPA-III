import EPPAIII.BlockSystems.SmallHostPrimitiveEquality
import EPPAIII.CliqueCovers.RegularGraphIndependent

/-!
# The strict small-host rank-three reduction without Neumann separation

For a positive-degree regular graph on m vertices, every independent
set has size at most m/2. Apply this to each unordered pair-orbit
graph of the transitive host H. If the selected copy G occupies more
than half the vertices, no pair orbit can be absent from G.

The resulting pair coverage plus EPPA implies the full ordered
edge/nonedge orbit condition. This avoids the finite-group averaging
argument (Neumann's separation lemma) in the printed proof and
remains valid in every small-order boundary case.
-/

namespace EPPAIII.BlockSystems

/-- In a vertex-transitive graph H, every nonempty orbit of unordered
pairs meets any embedded vertex subset occupying more than half the
vertices. No EPPA assumption is necessary for this fact. -/
theorem large_selected_set_meets_every_unordered_pair_orbit
    {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph W)
    (e : V ↪ W)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hLarge : Fintype.card W < 2 * Fintype.card V)
    (a b : W) (hab : a ≠ b) :
    ∃ x y : V,
      (unorderedPairOrbitGraph H a b hab).Adj (e x) (e y) := by
  classical
  let F : SimpleGraph W := unorderedPairOrbitGraph H a b hab
  letI : Nonempty W := ⟨a⟩
  have hTransF :
      EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms F :=
    unorderedPairOrbitGraph_vertex_transitive H a b hab hTrans
  by_contra hNo
  have hNoSelected :
      ∀ x y : V, ¬ F.Adj (e x) (e y) := by
    intro x y h
    exact hNo ⟨x,y,h⟩
  obtain ⟨d,hRegular⟩ :=
    EPPAIII.CliqueCovers.regular_of_transitive_graph F hTransF
  have hEdge : F.Adj a b :=
    unorderedPairOrbitGraph_base_edge H a b hab
  have hPositiveDegree : 0 < F.degree a := by
    have hv : b ∈ F.neighborFinset a :=
      (F.mem_neighborFinset a b).mpr hEdge
    have hvPos : 0 < (F.neighborFinset a).card :=
      Finset.card_pos.mpr ⟨b,hv⟩
    change 0 < (F.neighborFinset a).card
    exact hvPos
  have hd : 0 < d := by
    rw [hRegular a] at hPositiveDegree
    exact hPositiveDegree
  let S : Finset W := (Finset.univ : Finset V).image e
  have hSCard : S.card = Fintype.card V := by
    simpa [S] using
      (Finset.card_image_of_injective
        (Finset.univ : Finset V) e.injective)
  have hIndependent : F.IsIndepSet (S : Set W) := by
    intro u hu v hv huv
    change u ∈ S at hu
    change v ∈ S at hv
    obtain ⟨x,_,hux⟩ := Finset.mem_image.mp hu
    obtain ⟨y,_,hvy⟩ := Finset.mem_image.mp hv
    subst u
    subst v
    exact hNoSelected x y
  have hBound :=
    EPPAIII.CliqueCovers.regular_graph_independent_card_le_half
      F d hd hRegular S hIndependent
  rw [hSCard] at hBound
  omega

/-- The strict |H| < 2|G| assumption supplies full ordered pair
coverage for the distinguished copy, without primitivity or EPPA. -/
theorem large_selected_set_pair_coverage
    {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hLarge : Fintype.card W < 2 * Fintype.card V) :
    HasSelectedPairCoverage H e := by
  intro u v huv
  obtain ⟨x,y,hEdge⟩ :=
    large_selected_set_meets_every_unordered_pair_orbit
      H e hTrans hLarge u v huv
  have hxy : x ≠ y := by
    intro heq
    exact ((unorderedPairOrbitGraph H u v huv).ne_of_adj hEdge)
      (by simpa [heq])
  rcases hEdge with ⟨q,hq,hPair⟩
  rcases hPair with ⟨hqu,hqv⟩ | ⟨hqu,hqv⟩
  · exact ⟨x,y,q,hxy,hq,hqu,hqv⟩
  · exact ⟨y,x,q,hxy.symm,hq,hqu,hqv⟩

/-- Complete strict-inequality part of the source-facing rank-three
proposition under the actual fixed-embedding EPPA interface:
one orbit on ordered edges, one on ordered nonedges. -/
theorem transitive_eppa_small_strict_has_pair_orbits
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSmall : Fintype.card W < 2 * Fintype.card V) :
    HasOrderedPairOrbitByStatus H := by
  exact eppa_pair_status_orbits_of_selected_coverage
    G H e heppa (large_selected_set_pair_coverage
      H e hTrans hSmall)

end EPPAIII.BlockSystems
