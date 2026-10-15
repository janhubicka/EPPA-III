import EPPAIII.BlockSystems.OutsideProfileMultiplicity

/-!
# Transporting genuine EPPA lifts to canonical outside labels

A full automorphism p of the selected base has some EPPA extension q.
Neighbourhood profiles then transform by forward image under p.
If an injective profile map labels the complementary half using
a family of profiles equivariant under p, uniqueness forces q to
act on those outside vertices according to p.

The resulting induced outside graph is genuinely p-invariant.
Neither a coherent family of EPPA extensions nor an a priori
identification of the two halves is assumed.
-/

namespace EPPAIII.BlockSystems

/-- The translated profile defined using p.symm is precisely the
forward image of the finite neighbourhood set under p. -/
theorem translated_finite_profile_eq_image {V W : Type*}
    [Fintype V]
    (H : SimpleGraph W) (e : V ↪ W)
    (w : W) (p : Equiv.Perm V) :
    translatedFiniteProfile H e w p =
      (finiteNeighbourhoodProfile H e w).image p := by
  classical
  ext v
  have hLeft :
      v ∈ translatedFiniteProfile H e w p ↔
        H.Adj w (e (p.symm v)) := by
    simp [translatedFiniteProfile]
  have hRight :
      v ∈ (finiteNeighbourhoodProfile H e w).image p ↔
        H.Adj w (e (p.symm v)) := by
    constructor
    · intro hv
      obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp hv
      have hInv : p.symm v = u := by
        calc
          p.symm v = p.symm (p u) :=
            congrArg p.symm huv.symm
          _ = u := p.symm_apply_apply u
      simpa [finiteNeighbourhoodProfile, hInv] using hu
    · intro hv
      apply Finset.mem_image.mpr
      refine ⟨p.symm v, ?_, by simp⟩
      simpa [finiteNeighbourhoodProfile] using hv
  exact hLeft.trans hRight.symm

/-- An actual EPPA-compatible host automorphism acts on finite
selected neighbourhood profiles by applying p to the profile. -/
theorem finite_profile_image_under_host_automorphism
    {V W : Type*} [Fintype V]
    (H : SimpleGraph W) (e : V ↪ W)
    (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hCompat : ∀ v : V, q (e v) = e (p v))
    (w : W) :
    finiteNeighbourhoodProfile H e (q w) =
      (finiteNeighbourhoodProfile H e w).image p := by
  calc
    finiteNeighbourhoodProfile H e (q w) =
        translatedFiniteProfile H e w p :=
      finite_profile_transport H e w p q hCompat hq
    _ = (finiteNeighbourhoodProfile H e w).image p :=
      translated_finite_profile_eq_image H e w p

/-- Once unique profiles label the outside vertices and commute
with the base automorphism p, one actual EPPA lift transports each
outside label x to p x. Hence the actual outside graph is p-invariant. -/
theorem canonical_outside_graph_automorphism
    {V W : Type*}
    [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (p : Equiv.Perm V) (hp : IsGraphAutomorphism G p)
    (label : V → Finset V) (outside : V → W)
    (hOutside : ∀ x : V, outside x ∈ finiteOutside e)
    (hProfile : ∀ x : V,
      finiteNeighbourhoodProfile H e (outside x) = label x)
    (hInjective : Set.InjOn (finiteNeighbourhoodProfile H e)
      (finiteOutside e : Set W))
    (hLabelEq : ∀ x : V, label (p x) = (label x).image p) :
    IsGraphAutomorphism (H.comap outside) p := by
  classical
  obtain ⟨q,hq,hCompat⟩ := eppa_lifts_total G H e heppa p hp
  have hLiftOutside (x : V) : q (outside x) ∈ finiteOutside e := by
    have hx : outside x ∉ Set.range e := by
      simpa [finiteOutside] using hOutside x
    have hqx := lift_preserves_outside e p q hCompat
      (outside x) hx
    simpa [finiteOutside] using hqx
  have hLiftProfile (x : V) :
      finiteNeighbourhoodProfile H e (q (outside x)) =
        finiteNeighbourhoodProfile H e (outside (p x)) := by
    calc
      finiteNeighbourhoodProfile H e (q (outside x)) =
          (finiteNeighbourhoodProfile H e (outside x)).image p :=
        finite_profile_image_under_host_automorphism
          H e p q hq hCompat (outside x)
      _ = (label x).image p := congrArg (fun s => s.image p) (hProfile x)
      _ = label (p x) := (hLabelEq x).symm
      _ = finiteNeighbourhoodProfile H e (outside (p x)) :=
        (hProfile (p x)).symm
  have hOutsideAction (x : V) :
      q (outside x) = outside (p x) :=
    hInjective (hLiftOutside x) (hOutside (p x)) (hLiftProfile x)
  intro x y
  change H.Adj (outside x) (outside y) ↔
    H.Adj (outside (p x)) (outside (p y))
  calc
    H.Adj (outside x) (outside y) ↔
        H.Adj (q (outside x)) (q (outside y)) := hq _ _
    _ ↔ H.Adj (outside (p x)) (outside (p y)) := by
      rw [hOutsideAction x, hOutsideAction y]

end EPPAIII.BlockSystems
