import EPPAIII.BlockSystems.RookThreeSubsetAction
import EPPAIII.EPPA.ProfileOrbitBound

/-!
# Multiplicities of outside neighbourhood profiles are EPPA-invariant

The elementary EPPA orbit-size bound loses information when many
outside vertices have the same selected neighbourhood. To complete
the R3 exceptional case one needs the stronger multiset statement:
every full automorphism of the base preserves the multiplicity of
each outside profile under its induced action on finite subsets.

The proof uses ONE genuine EPPA lift of each base automorphism.
The lift need not be chosen coherently across the automorphism
group. This is also reusable for other finite EPPA witnesses.
-/

namespace EPPAIII.BlockSystems

/-- Number of complementary host vertices having exactly the
given finite neighbourhood in the selected base copy. -/
noncomputable def outsideProfileMultiplicity {V W : Type*}
    [Fintype V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W) (S : Finset V) : ℕ := by
  classical
  exact ((finiteOutside e).filter
    (fun w => finiteNeighbourhoodProfile H e w = S)).card

/-- Each full base automorphism preserves all multiplicities
of outside profiles, even without coherent EPPA extensions. -/
theorem outside_profile_multiplicity_base_automorphism
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (p : Equiv.Perm V) (hp : IsGraphAutomorphism G p)
    (S : Finset V) :
    outsideProfileMultiplicity H e S =
      outsideProfileMultiplicity H e (S.image p) := by
  classical
  obtain ⟨q,hq,hCompat⟩ := eppa_lifts_total G H e heppa p hp
  have hOutside (w : W) :
      w ∈ finiteOutside e ↔ q w ∈ finiteOutside e := by
    simp only [finiteOutside, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · exact lift_preserves_outside e p q hCompat w
    · intro hqw hw
      obtain ⟨v,hv⟩ := hw
      apply hqw
      exact ⟨p v, (hCompat v).symm.trans (congrArg q hv)⟩
  have hMember (w : W) (v : V) :
      v ∈ finiteNeighbourhoodProfile H e w ↔
        p v ∈ finiteNeighbourhoodProfile H e (q w) := by
    simpa [finiteNeighbourhoodProfile,neighbourhoodProfile] using
      (profile_equivariant H e p q hq hCompat w v)
  have hProfile (w : W) :
      finiteNeighbourhoodProfile H e (q w) =
        (finiteNeighbourhoodProfile H e w).image p := by
    ext v
    constructor
    · intro hv
      have hu := (hMember w (p.symm v)).mpr (by simpa using hv)
      exact Finset.mem_image.mpr ⟨p.symm v,hu,by simp⟩
    · intro hv
      obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp hv
      have hu' := (hMember w u).mp hu
      simpa [huv] using hu'
  let L : Finset W := (finiteOutside e).filter
    (fun w => finiteNeighbourhoodProfile H e w = S)
  let R : Finset W := (finiteOutside e).filter
    (fun w => finiteNeighbourhoodProfile H e w = S.image p)
  have hIff (w : W) : w ∈ L ↔ q w ∈ R := by
    constructor
    · intro hw
      obtain ⟨hOut,hS⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr
        ⟨(hOutside w).mp hOut,by rw [hProfile w,hS]⟩
    · intro hw
      obtain ⟨hOut,hS⟩ := Finset.mem_filter.mp hw
      have hEqual : (finiteNeighbourhoodProfile H e w).image p =
          S.image p := by
        calc
          (finiteNeighbourhoodProfile H e w).image p =
              finiteNeighbourhoodProfile H e (q w) :=
            (hProfile w).symm
          _ = S.image p := hS
      exact Finset.mem_filter.mpr
        ⟨(hOutside w).mpr hOut,
          (Finset.image_injective p.injective) hEqual⟩
  change L.card = R.card
  refine Finset.card_bij'
    (fun w _ => q w) (fun w _ => q.symm w) ?_ ?_ ?_ ?_
  · intro w hw
    exact (hIff w).mp hw
  · intro w hw
    apply (hIff (q.symm w)).mpr
    simpa using hw
  · intro w hw
    simp
  · intro w hw
    simp

/-- The total multiplicity of all occurring outside profiles
is precisely the number of vertices outside the selected copy. -/
theorem outside_profile_multiplicity_sum
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W) :
    (∑ S ∈ (finiteOutside e).image
      (finiteNeighbourhoodProfile H e),
        outsideProfileMultiplicity H e S) =
      (finiteOutside e).card := by
  classical
  simpa [outsideProfileMultiplicity] using
    (Finset.card_eq_sum_card_image
      (finiteNeighbourhoodProfile H e) (finiteOutside e)).symm

/-- Apply the preceding multiset invariant to the 72 explicit,
genuine automorphisms of the nine-vertex rook graph. -/
theorem rook_outside_profile_multiplicity_invariant
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 3 × Fin 3) ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (S : Finset (Fin 3 × Fin 3))
    (p : rookAutParameter) :
    outsideProfileMultiplicity H e S =
      outsideProfileMultiplicity H e
        (S.image (rookParameterizedAut p)) :=
  outside_profile_multiplicity_base_automorphism
    rookThreeGraph H e heppa (rookParameterizedAut p)
      (rookParameterizedAut_graph_automorphism p) S

end EPPAIII.BlockSystems
