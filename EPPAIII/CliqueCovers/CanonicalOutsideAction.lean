import EPPAIII.CliqueCovers.OutsideProfileBijection

/-!
# Canonical action of base automorphisms on the outside half

When the outside-neighbourhood profile map is injective, an
automorphism of H preserving the distinguished G is entirely
determined by its action on G: every outside vertex moves to the
unique vertex with the translated base-neighbourhood profile.

This is the missing coherence principle needed for the natural
wreath-product action in the one-partial proof of Lemma 3.7.
Importantly, it is a *consequence* of the saturated profile orbit;
we never choose EPPA extensions coherently as a hypothesis.
-/

namespace EPPAIII.CliqueCovers

/-- If the outside profile map is injective, two graph automorphisms
with the same action on the distinguished copy coincide at every
outside vertex. The witness w below supplies the saturation
hypothesis for the injectivity theorem. -/
theorem saturated_lifts_agree_outside {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (p : Equiv.Perm (Fin s × Fin t))
    (q₁ q₂ : Equiv.Perm W)
    (hq₁ : IsGraphAutomorphism H q₁)
    (hq₂ : IsGraphAutomorphism H q₂)
    (hCompat₁ : ∀ v, q₁ (e v) = e (p v))
    (hCompat₂ : ∀ v, q₂ (e v) = e (p v))
    (u : W) (hu : u ∉ Set.range e) :
    q₁ u = q₂ u := by
  classical
  have hInj :=
    (eppa_saturated_outside_profile_bijection
      H e heppa hOrder w hw r k hR hSat).1
  have hOutside₁ : q₁ u ∉ Set.range e :=
    lift_preserves_outside e p q₁ hCompat₁ u hu
  have hOutside₂ : q₂ u ∉ Set.range e :=
    lift_preserves_outside e p q₂ hCompat₂ u hu
  have hMem₁ : q₁ u ∈ finiteOutside e := by
    simpa [finiteOutside] using hOutside₁
  have hMem₂ : q₂ u ∈ finiteOutside e := by
    simpa [finiteOutside] using hOutside₂
  have hProfile :
      finiteNeighbourhoodProfile H e (q₁ u) =
        finiteNeighbourhoodProfile H e (q₂ u) := by
    calc
      finiteNeighbourhoodProfile H e (q₁ u) =
          translatedFiniteProfile H e u p :=
        finite_profile_transport H e u p q₁ hCompat₁ hq₁
      _ = finiteNeighbourhoodProfile H e (q₂ u) :=
        (finite_profile_transport H e u p q₂ hCompat₂ hq₂).symm
  exact hInj hMem₁ hMem₂ hProfile

/-- Under saturation, agreeing on all base vertices implies
equality of the two whole host automorphisms. No coherent choice
of EPPA extensions is assumed. -/
theorem saturated_lifts_unique {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (p : Equiv.Perm (Fin s × Fin t))
    (q₁ q₂ : Equiv.Perm W)
    (hq₁ : IsGraphAutomorphism H q₁)
    (hq₂ : IsGraphAutomorphism H q₂)
    (hCompat₁ : ∀ v, q₁ (e v) = e (p v))
    (hCompat₂ : ∀ v, q₂ (e v) = e (p v)) :
    q₁ = q₂ := by
  apply Equiv.ext
  intro u
  by_cases hu : u ∈ Set.range e
  · obtain ⟨v, rfl⟩ := hu
    rw [hCompat₁ v, hCompat₂ v]
  · exact saturated_lifts_agree_outside H e heppa hOrder
      w hw r k hR hSat p q₁ q₂
      hq₁ hq₂ hCompat₁ hCompat₂ u hu

/-- If a proper coordinate size occurs exactly once, Claim 3.9
supplies saturation, so base-compatible lifts are unique on H. -/
theorem unique_partial_base_aut_has_unique_extension {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (k : ℕ) (hs : 0 < s) (hk : 0 < k) (hkt : k < t)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) k).card = 1)
    (p : Equiv.Perm (Fin s × Fin t))
    (q₁ q₂ : Equiv.Perm W)
    (hq₁ : IsGraphAutomorphism H q₁)
    (hq₂ : IsGraphAutomorphism H q₂)
    (hCompat₁ : ∀ v, q₁ (e v) = e (p v))
    (hCompat₂ : ∀ v, q₂ (e v) = e (p v)) :
    q₁ = q₂ := by
  classical
  have hExtreme : k = 1 ∨ k + 1 = t :=
    eppa_clique_partial_degree_extreme H e heppa
      w hw k hs hk hkt
      (by rw [hUnique]; decide)
      (le_of_eq (finiteOutside_card_clique_union e hOrder))
  have hChoose : Nat.choose t k = t := by
    rcases hExtreme with hOne | hCos
    · simp [hOne]
    · have h : t - k = 1 := by omega
      calc
        Nat.choose t k = Nat.choose t (t - k) :=
          (Nat.choose_symm (Nat.le_of_lt hkt)).symm
        _ = Nat.choose t 1 := by rw [h]
        _ = t := Nat.choose_one_right t
  have hSat : Nat.choose s 1 * (Nat.choose t k)^1 = s * t := by
    simp [hChoose]
  exact saturated_lifts_unique H e heppa hOrder w hw
    1 k hUnique hSat p q₁ q₂ hq₁ hq₂ hCompat₁ hCompat₂

end EPPAIII.CliqueCovers
