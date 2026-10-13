import EPPAIII.CliqueCovers.WagnerOutsideLabels
import EPPAIII.CliqueCovers.WagnerProfileGenerators
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# Genuine EPPA extensions act as the three Wagner square generators

The canonical saturated Bool×Bool outside labels record the actual
two singleton slices of each outside neighbourhood. Each of the
three base wreath automorphisms transports the corresponding finite
profile exactly by a square flip or coordinate swap.

EPPA gives a host automorphism extending that base permutation.
Profile injectivity at saturation then forces its restriction to the
actual outside half to act on the corner labels by that square
generator. The proof does not require choosing lifts coherently.
-/

namespace EPPAIII.CliqueCovers

/-- Actual outside profiles at a labelled corner equal the concrete
two-element square profile. -/
theorem saturatedWagnerOutsideEquiv_profile
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (x : Bool × Bool) :
    finiteNeighbourhoodProfile H e
      (saturatedWagnerOutsideEquiv H e heppa hOrder
        w hw hBoth x).val = squareProfile x := by
  apply squareProfile_eq_of_slices
  · exact saturatedWagnerOutsideEquiv_first
      H e heppa hOrder w hw hBoth x
  · exact saturatedWagnerOutsideEquiv_second
      H e heppa hOrder w hw hBoth x

/-- An arbitrary base automorphism whose square profiles transform
by g has a genuine EPPA extension acting by g on all four outside
vertices. No group-homomorphic choice of extensions is made. -/
theorem eppa_wagner_outside_generator
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (p : Equiv.Perm (Fin 2 × Fin 2))
    (hp : IsGraphAutomorphism (cliqueUnion 2 2) p)
    (g : Equiv.Perm (Bool × Bool))
    (hMap : ∀ x : Bool × Bool,
      (squareProfile x).map p.toEmbedding = squareProfile (g x)) :
    ∃ Q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) Q ∧
      ∀ x : Bool × Bool,
        Q (saturatedWagnerOutsideEquiv
          H e heppa hOrder w hw hBoth x) =
          saturatedWagnerOutsideEquiv
            H e heppa hOrder w hw hBoth (g x) := by
  classical
  obtain ⟨q,hq,hCompat⟩ :=
    eppa_lifts_total (cliqueUnion 2 2) H e heppa p hp
  let label := saturatedWagnerOutsideEquiv H e heppa hOrder w hw hBoth
  let Q := outsideLiftPermutation e p q hCompat
  refine ⟨Q, outsideLiftPermutation_graphAut
    H e p q hCompat hq, ?_⟩
  intro x
  have hSource := saturatedWagnerOutsideEquiv_profile
    H e heppa hOrder w hw hBoth x
  have hTarget := saturatedWagnerOutsideEquiv_profile
    H e heppa hOrder w hw hBoth (g x)
  have hProfile :
      finiteNeighbourhoodProfile H e (q (label x).val) =
        finiteNeighbourhoodProfile H e (label (g x)).val := by
    calc
      finiteNeighbourhoodProfile H e (q (label x).val) =
        translatedFiniteProfile H e (label x).val p :=
          finite_profile_transport H e (label x).val
            p q hCompat hq
      _ = (finiteNeighbourhoodProfile H e (label x).val).map
            p.toEmbedding :=
        translatedFiniteProfile_eq_map H e (label x).val p
      _ = squareProfile (g x) := by
        rw [hSource]
        exact hMap x
      _ = finiteNeighbourhoodProfile H e (label (g x)).val :=
        hTarget.symm
  have hInjective :=
    (eppa_saturated_outside_profile_bijection H e heppa hOrder
      w hw 2 1 hBoth wagner_square_choice_saturation).1
  apply Subtype.ext
  have hVal : (Q (label x)).val = q (label x).val := rfl
  rw [hVal]
  exact hInjective (Q (label x)).property
    (label (g x)).property hProfile

/-- The first independent base-clique flip acts as the first square
coordinate flip on the actual outside half. -/
theorem eppa_wagner_outside_flipFirst
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2) :
    ∃ Q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) Q ∧
      ∀ x : Bool × Bool,
        Q (saturatedWagnerOutsideEquiv H e heppa hOrder w hw hBoth x) =
          saturatedWagnerOutsideEquiv H e heppa hOrder
            w hw hBoth (squareFlipFirst x) :=
  eppa_wagner_outside_generator H e heppa hOrder w hw hBoth
    squareBaseFlipFirst squareBaseFlipFirst_graphAut
      squareFlipFirst squareProfile_flipFirst

theorem eppa_wagner_outside_flipSecond
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2) :
    ∃ Q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) Q ∧
      ∀ x : Bool × Bool,
        Q (saturatedWagnerOutsideEquiv H e heppa hOrder w hw hBoth x) =
          saturatedWagnerOutsideEquiv H e heppa hOrder
            w hw hBoth (squareFlipSecond x) :=
  eppa_wagner_outside_generator H e heppa hOrder w hw hBoth
    squareBaseFlipSecond squareBaseFlipSecond_graphAut
      squareFlipSecond squareProfile_flipSecond

theorem eppa_wagner_outside_swapCoordinates
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2) :
    ∃ Q : Equiv.Perm {u : W // u ∈ finiteOutside e},
      IsGraphAutomorphism (outsideInducedGraph H e) Q ∧
      ∀ x : Bool × Bool,
        Q (saturatedWagnerOutsideEquiv H e heppa hOrder w hw hBoth x) =
          saturatedWagnerOutsideEquiv H e heppa hOrder
            w hw hBoth (squareSwapCoordinates x) :=
  eppa_wagner_outside_generator H e heppa hOrder w hw hBoth
    squareBaseSwapCoordinates squareBaseSwapCoordinates_graphAut
      squareSwapCoordinates squareProfile_swapCoordinates

end EPPAIII.CliqueCovers
