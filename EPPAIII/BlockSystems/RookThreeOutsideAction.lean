import EPPAIII.BlockSystems.OutsideProfileCanonicalAction
import EPPAIII.BlockSystems.RookThreeNeighbourhoodOrbits
import EPPAIII.BlockSystems.RookThreeInvariantFourForms

/-!
# The rook action on canonically labelled complementary vertices

For any of the 72 genuine rook automorphisms p, the open-neighbourhood
profile N(x) and the strict nonneighbourhood profile M(x) both transform
by forward image. Hence if the actual outside vertices have unique
profiles N(x), respectively M(x), every EPPA lift of p acts on them by
x ↦ p(x).

This identifies the *actual* induced outside graph as invariant under
the full rook action and therefore as one of four graph forms. No
equivariant outside labelling or coherent lifts are postulated.
-/

namespace EPPAIII.BlockSystems

/-- Genuine rook automorphisms transport open neighbourhoods
to the open neighbourhood of the image. -/
theorem rook_open_neighbourhood_equivariant
    (p : rookAutParameter) (x : rookVertex) :
    rookOpenNeighbourhood (rookParameterizedAut p x) =
      (rookOpenNeighbourhood x).image (rookParameterizedAut p) := by
  classical
  let q := rookParameterizedAut p
  have hq : IsGraphAutomorphism rookThreeGraph q :=
    rookParameterizedAut_graph_automorphism p
  ext y
  constructor
  · intro hy
    let u : rookVertex := q.symm y
    have hAdj : rookThreeGraph.Adj (q x) y := by
      simpa [rookOpenNeighbourhood] using hy
    have hBase : rookThreeGraph.Adj x u := (hq x u).mpr (by
      simpa [u] using hAdj)
    exact Finset.mem_image.mpr
      ⟨u, by simpa [rookOpenNeighbourhood] using hBase, by simp [u]⟩
  · intro hy
    obtain ⟨u,hu,huy⟩ := Finset.mem_image.mp hy
    have hAdj : rookThreeGraph.Adj x u := by
      simpa [rookOpenNeighbourhood] using hu
    have hNew : rookThreeGraph.Adj (q x) (q u) := (hq x u).mp hAdj
    have hAdjY : rookThreeGraph.Adj (q x) y := by
      simpa [q, ← huy] using hNew
    simpa [rookOpenNeighbourhood] using hAdjY

/-- Genuine rook automorphisms also transport strict nonneighbourhoods. -/
theorem rook_strict_nonneighbours_equivariant
    (p : rookAutParameter) (x : rookVertex) :
    rookStrictNonneighbours (rookParameterizedAut p x) =
      (rookStrictNonneighbours x).image (rookParameterizedAut p) := by
  classical
  let q := rookParameterizedAut p
  have hq : IsGraphAutomorphism rookThreeGraph q :=
    rookParameterizedAut_graph_automorphism p
  ext y
  constructor
  · intro hy
    let u : rookVertex := q.symm y
    have hInfo : y ≠ q x ∧ ¬ rookThreeGraph.Adj (q x) y := by
      simpa [rookStrictNonneighbours] using hy
    have huNe : u ≠ x := by
      intro h
      apply hInfo.1
      calc
        y = q u := (q.apply_symm_apply y).symm
        _ = q x := congrArg q h
    have huNo : ¬ rookThreeGraph.Adj x u := by
      intro h
      exact hInfo.2 (by simpa [u] using (hq x u).mp h)
    exact Finset.mem_image.mpr
      ⟨u, by simpa [rookStrictNonneighbours] using
        (And.intro huNe huNo), by simp [u]⟩
  · intro hy
    obtain ⟨u,hu,huy⟩ := Finset.mem_image.mp hy
    have hInfo : u ≠ x ∧ ¬ rookThreeGraph.Adj x u := by
      simpa [rookStrictNonneighbours] using hu
    have hNew : q u ≠ q x ∧ ¬ rookThreeGraph.Adj (q x) (q u) := by
      constructor
      · exact q.injective.ne hInfo.1
      · intro h
        exact hInfo.2 ((hq x u).mpr h)
    have hInfoY : y ≠ q x ∧ ¬ rookThreeGraph.Adj (q x) y := by
      simpa [q, ← huy] using hNew
    simpa [rookStrictNonneighbours] using hInfoY

/-- Under canonical neighbourhood or nonneighbourhood outside labels,
the induced outside graph is invariant under all rook automorphisms. -/
theorem rook_canonical_outside_graph_invariant
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (outside : rookVertex → W)
    (hOutside : ∀ x : rookVertex, outside x ∈ finiteOutside e)
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x, finiteNeighbourhoodProfile H e (outside x) =
        rookOpenNeighbourhood x) ∨
      (∀ x, finiteNeighbourhoodProfile H e (outside x) =
        rookStrictNonneighbours x)) :
    ∀ p : rookAutParameter,
      IsGraphAutomorphism (H.comap outside) (rookParameterizedAut p) := by
  intro p
  have hp := rookParameterizedAut_graph_automorphism p
  rcases hLabels with hOpen | hNon
  · exact canonical_outside_graph_automorphism
      rookThreeGraph H e heppa (rookParameterizedAut p) hp
      rookOpenNeighbourhood outside hOutside hOpen hInjective
      (rook_open_neighbourhood_equivariant p)
  · exact canonical_outside_graph_automorphism
      rookThreeGraph H e heppa (rookParameterizedAut p) hp
      rookStrictNonneighbours outside hOutside hNon hInjective
      (rook_strict_nonneighbours_equivariant p)

/-- Consequently the actual outside graph, in these canonical
coordinates, belongs to the four graph forms on the rook vertices. -/
theorem rook_canonical_outside_graph_four_forms
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (outside : rookVertex → W)
    (hOutside : ∀ x : rookVertex, outside x ∈ finiteOutside e)
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabels :
      (∀ x, finiteNeighbourhoodProfile H e (outside x) =
        rookOpenNeighbourhood x) ∨
      (∀ x, finiteNeighbourhoodProfile H e (outside x) =
        rookStrictNonneighbours x)) :
    H.comap outside = ⊥ ∨
      H.comap outside = rookThreeGraph ∨
      H.comap outside = rookThreeGraphᶜ ∨
      H.comap outside = ⊤ :=
  rook_invariant_graph_four_forms (H.comap outside)
    (rook_canonical_outside_graph_invariant
      H e heppa outside hOutside hInjective hLabels)

end EPPAIII.BlockSystems
