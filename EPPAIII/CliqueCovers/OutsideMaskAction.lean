import EPPAIII.CliqueCovers.OutsideTwinClasses
import EPPAIII.CliqueCovers.FullMaskOrbit
import EPPAIII.CliqueCovers.OutsideLiftTransport
import EPPAIII.CliqueCovers.WreathGenerators

/-!
# Actual outside clique-index masks are equivariant under EPPA lifts

For each vertex u outside the selected copy sK_t, record the
set of base clique indices i whose anchor e(i,a) is adjacent to u.

Every outer permutation of the base clique indices extends by EPPA
to a host automorphism that preserves the outside half. The induced
index mask is exactly its image under the outer permutation.
Furthermore, two outside vertices in the same closed-neighbourhood
class have equal masks. These are the two graph-level inputs needed
to bound the full-index-mask orbit by the s outside twin classes.

No quotient-class labelling or coherent system of EPPA extensions
is chosen or assumed.
-/

namespace EPPAIII.CliqueCovers

/-- Neighbourhood mask of a vertex relative to the selected
anchor point a in each base clique. -/
noncomputable def outsideIndexMask {s t : ℕ} {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t) (u : W) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter (fun i => H.Adj u (e (i,a)))

/-- Two outside vertices with the same closed neighbourhood
have exactly the same selected clique-index adjacency mask. -/
theorem outsideIndexMask_eq_of_closed_twins {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W) (a : Fin t)
    (u v : W) (hu : u ∉ Set.range e) (hv : v ∉ Set.range e)
    (hSame : SameClosedNeighbourhood H u v) :
    outsideIndexMask H e a u = outsideIndexMask H e a v := by
  classical
  ext i
  have hNeU : e (i,a) ≠ u := by
    intro h
    exact hu ⟨(i,a),h⟩
  have hNeV : e (i,a) ≠ v := by
    intro h
    exact hv ⟨(i,a),h⟩
  have hMem := congrArg
    (fun S : Set W => e (i,a) ∈ S) hSame
  simpa [outsideIndexMask, closedNeighbourhood,
    hNeU, hNeV] using hMem

/-- A compatible outer-permutation EPPA lift acts on the
actual outside index mask exactly by that outer permutation. -/
theorem outsideIndexMask_outer_lift {s t : ℕ} {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t) (u : W)
    (p : Equiv.Perm (Fin s)) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hCompat : ∀ x : Fin s × Fin t,
      q (e x) = e (outerPermutation p x)) :
    outsideIndexMask H e a (q u) =
      (outsideIndexMask H e a u).map p.toEmbedding := by
  classical
  ext i
  simp only [outsideIndexMask, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    have hInv :
        H.Adj u (e (p.symm i,a)) := by
      have hh := (hq u (e (p.symm i,a))).mpr
      apply hh
      simpa [hCompat (p.symm i,a), outerPermutation] using h
    apply Finset.mem_map.mpr
    refine ⟨p.symm i, ?_, by simp⟩
    simpa [outsideIndexMask] using hInv
  · intro h
    obtain ⟨j,hj,hji⟩ := Finset.mem_map.mp h
    have hjAdj : H.Adj u (e (j,a)) := by
      simpa [outsideIndexMask] using hj
    have hNew := (hq u (e (j,a))).mp hjAdj
    rw [hCompat (j,a)] at hNew
    have hpj : p j = i := by
      first
      | simpa only [Equiv.toEmbedding_apply] using hji
      | simpa only [Equiv.toEmbedding_apply] using hji.symm
    have hNew' : H.Adj (q u) (e (p j,a)) := by
      change H.Adj (q u) (e (p j,a)) at hNew
      exact hNew
    exact hpj ▸ hNew'

/-- Every mask in the full permutation orbit of an outside
vertex's mask is realized by another genuine outside vertex. -/
theorem eppa_outer_mask_orbit_realized {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (a : Fin t) (w : W) (hw : w ∉ Set.range e)
    (R : Finset (Fin s))
    (hR : R ∈ outerMaskOrbit (outsideIndexMask H e a w)) :
    ∃ u : W, u ∉ Set.range e ∧ outsideIndexMask H e a u = R := by
  classical
  unfold outerMaskOrbit at hR
  obtain ⟨p,_,hpR⟩ := Finset.mem_image.mp hR
  obtain ⟨q,hq,hCompat⟩ :=
    eppa_lifts_total (cliqueUnion s t) H e heppa
      (outerPermutation p) (outerPermutation_aut p)
  refine ⟨q w, lift_preserves_outside e
    (outerPermutation p) q hCompat w hw, ?_⟩
  exact (outsideIndexMask_outer_lift H e a w p q hq hCompat).trans hpR

end EPPAIII.CliqueCovers
