import EPPAIII.EPPA.ProfileAction

/-!
# The finite neighbourhood-profile orbit bound from EPPA

For a distinguished finite induced G in H, every automorphism of G
extends to H and preserves the complement of the selected copy.
Consequently every translate of the profile of an outside vertex w
is realized by another outside vertex, even if the extending host
automorphism moves all outside cliques.

This is the precise common input to the short orbit repair of
Claim 3.9 and the direct proof of Lemma 3.7. It never assumes
individual outside cliques D_j are fixed.
-/

namespace EPPAIII

/-- The neighbourhood profile of a vertex of H, presented as a
finite subset of the distinguished base vertex type. -/
noncomputable def finiteNeighbourhoodProfile {V W : Type*}
    [Fintype V] (H : SimpleGraph W) (e : V ↪ W)
    (w : W) : Finset V := by
  classical
  exact Finset.univ.filter (fun v : V => H.Adj w (e v))

/-- The orbit of the outside neighbourhood profile under all
automorphisms of G. Each translate is the forward image of the
original profile under the corresponding base permutation. -/
noncomputable def finiteProfileOrbit {V W : Type*}
    [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (w : W) : Finset (Finset V) := by
  classical
  exact
    (Finset.univ.filter (fun p : Equiv.Perm V =>
      IsGraphAutomorphism G p)).image
      (fun p =>
        Finset.univ.filter (fun v : V => H.Adj w (e (p.symm v))))

/-- The finite set of host vertices outside the selected copy. -/
noncomputable def finiteOutside {V W : Type*} [Fintype W]
    (e : V ↪ W) : Finset W := by
  classical
  exact Finset.univ.filter (fun w : W => w ∉ Set.range e)

/-- The finite profile of an EPPA extension is the prescribed
translate of the profile of w. This equality is derived from the
pointwise profile-transport theorem, not from any coherent choice
of extensions. -/
theorem finite_profile_transport {V W : Type*}
    [Fintype V] (H : SimpleGraph W) (e : V ↪ W)
    (w : W) (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hCompat : ∀ v : V, q (e v) = e (p v))
    (hq : IsGraphAutomorphism H q) :
    finiteNeighbourhoodProfile H e (q w) =
      (Finset.univ : Finset V).filter
        (fun v : V => H.Adj w (e (p.symm v))) := by
  classical
  ext v
  simp only [finiteNeighbourhoodProfile, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have h := profile_equivariant H e p q hq hCompat w (p.symm v)
  simpa [neighbourhoodProfile] using h.symm

/-- **EPPA orbit-size bound.** The orbit of the neighbourhood
profile of any outside vertex w is realized among the outside
vertices of H. In particular, its number of distinct profiles
cannot exceed the size of the complementary half.

No transitivity of H, no regularity, and no partition into D_j
cliques is assumed here. -/
theorem finite_profile_orbit_card_le_outside {V W : Type*}
    [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (w : W) (hw : w ∉ Set.range e) :
    (finiteProfileOrbit G H e w).card ≤ (finiteOutside e).card := by
  classical
  have hSubset :
      finiteProfileOrbit G H e w ⊆
        (finiteOutside e).image (finiteNeighbourhoodProfile H e) := by
    intro S hS
    obtain ⟨p,hp,hProfile⟩ := Finset.mem_image.mp hS
    have hpAuto : IsGraphAutomorphism G p := by
      exact (Finset.mem_filter.mp hp).2
    obtain ⟨q,hq,hOutside,hTrans⟩ :=
      eppa_profiles_transport G H e heppa p hpAuto w hw
    have hCompat (v : V) : q (e v) = e (p v) := by
      -- The packaged orbit transport theorem supplies the profile
      -- identity but does not expose the compatibility witness;
      -- choose a fresh total EPPA extension with that witness.
      obtain ⟨q',hq',hcompat'⟩ := eppa_lifts_total G H e heppa p hpAuto
      exact hcompat' v
    -- Use one total extension consistently for compatibility,
    -- the outside vertex, and the transported profile.
    obtain ⟨q',hq',hCompat'⟩ := eppa_lifts_total G H e heppa p hpAuto
    have hOutside' : q' w ∉ Set.range e :=
      lift_preserves_outside e p q' hCompat' w hw
    refine Finset.mem_image.mpr ⟨q' w, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hOutside'⟩
    · have hh :=
        finite_profile_transport H e w p q' hCompat' hq'
      exact hh.trans hProfile
  calc
    (finiteProfileOrbit G H e w).card ≤
        ((finiteOutside e).image (finiteNeighbourhoodProfile H e)).card :=
      Finset.card_le_card hSubset
    _ ≤ (finiteOutside e).card := Finset.card_image_le

end EPPAIII
