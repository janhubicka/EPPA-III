import EPPAIII.BlockSystems.RookThreeEppaCanonicalOutside
import EPPAIII.BlockSystems.OutsideProfileEquiv

/-!
# A genuine outside-half equivalence from unique neighbourhood labels

A family of distinct finite selected-base neighbourhood profiles can
label the complementary half of a host provided its image is precisely
that family and the outside profile map is injective. We explicitly
construct the equivalence V ≃ outside(H), without choosing equivariant
EPPA extensions.

For an 18-vertex EPPA host of R3 with cross-degree four, earlier
proofs supply these hypotheses and identify the family with either
the rook open neighbourhoods or the strict nonneighbourhoods.
Thus we obtain the actual outside equivalence needed to transport
the complementary induced graph to canonical rook coordinates.
-/

namespace EPPAIII.BlockSystems

/-- A uniquely realised equivariant family of finite profiles gives
an actual equivalence from base labels onto the outside half. -/
theorem outside_profile_label_family_equiv
    {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (label : V → Finset V)
    (hLabelInj : Function.Injective label)
    (hImage :
      (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
        (Finset.univ : Finset V).image label)
    (hInj : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W)) :
    ∃ f : V ≃ {w : W // w ∈ finiteOutside e},
      ∀ x : V,
        finiteNeighbourhoodProfile H e (f x).val = label x := by
  classical
  let P : W → Finset V := finiteNeighbourhoodProfile H e
  have hExists (x : V) :
      ∃ w : W, w ∈ finiteOutside e ∧ P w = label x := by
    have hx : label x ∈ (finiteOutside e).image P := by
      rw [hImage]
      exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    exact Finset.mem_image.mp hx
  let f : V → {w : W // w ∈ finiteOutside e} := fun x =>
    ⟨Classical.choose (hExists x), (Classical.choose_spec (hExists x)).1⟩
  have hfProfile (x : V) : P (f x).val = label x :=
    (Classical.choose_spec (hExists x)).2
  have hfInj : Function.Injective f := by
    intro x y hxy
    apply hLabelInj
    calc
      label x = P (f x).val := (hfProfile x).symm
      _ = P (f y).val := by rw [hxy]
      _ = label y := hfProfile y
  have hfSurj : Function.Surjective f := by
    intro w
    have hwImage : P w.val ∈ (Finset.univ : Finset V).image label := by
      rw [← hImage]
      exact Finset.mem_image.mpr ⟨w.val,w.property,rfl⟩
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hwImage
    refine ⟨x,?_⟩
    apply Subtype.ext
    apply hInj (f x).property w.property
    calc
      P (f x).val = label x := hfProfile x
      _ = P w.val := hx
  refine ⟨Equiv.ofBijective f ⟨hfInj,hfSurj⟩,?_⟩
  intro x
  exact hfProfile x

/-- R3 EPPA with uniform outside degree four produces a genuine
complementary-half equivalence carrying either all rook open
neighbourhoods or all rook strict nonneighbourhoods. -/
theorem rook_eppa_degree_four_outside_equiv
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 4) :
    ∃ f : rookVertex ≃ {w : W // w ∈ finiteOutside e},
      (∀ x : rookVertex,
        finiteNeighbourhoodProfile H e (f x).val =
          rookOpenNeighbourhood x) ∨
      (∀ x : rookVertex,
        finiteNeighbourhoodProfile H e (f x).val =
          rookStrictNonneighbours x) := by
  classical
  obtain ⟨hCases,hInj⟩ :=
    rook_eppa_degree_four_outside_profile_orbit
      H e heppa h18 hDegree
  rcases hCases with hSquare | hOther
  · have hImage :
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          (Finset.univ : Finset rookVertex).image
            rookStrictNonneighbours := by
      rw [hSquare, rook_other_nine_orbit_eq_nonneighbourhoods]
    obtain ⟨f,hf⟩ :=
      outside_profile_label_family_equiv
        H e rookStrictNonneighbours
        rook_strict_nonneighbours_injective hImage hInj
    exact ⟨f,Or.inr hf⟩
  · have hImage :
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) =
          (Finset.univ : Finset rookVertex).image
            rookOpenNeighbourhood := by
      rw [hOther, rook_nine_orbit_eq_neighbourhoods]
    obtain ⟨f,hf⟩ :=
      outside_profile_label_family_equiv
        H e rookOpenNeighbourhood
        rook_open_neighbourhood_injective hImage hInj
    exact ⟨f,Or.inl hf⟩

end EPPAIII.BlockSystems
