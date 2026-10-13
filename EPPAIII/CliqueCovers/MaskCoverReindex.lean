import EPPAIII.CliqueCovers.MaskCoverNormalForms
import EPPAIII.CliqueCovers.FullMaskNormalForms

/-!
# Reindexing outside true-twin classes in the zero-partial case

The outer permutation of the selected clique indices is used to
normalize the masks. When the resulting family is singleton or
co-singleton, this permutation must be applied only to the OUTSIDE
clique labels, keeping the original distinguished selected copy fixed.

This file formalizes that reindexing and proves that each of the
four possible all-or-nothing mask families gives a uniform generalized
clique cover after a suitable permutation of the outside classes.

All graph conclusions are equalities of explicitly labelled
finite graphs; no EPPA hypotheses occur in this pure last step.
-/

namespace EPPAIII.CliqueCovers

/-- Permute the outside clique indices while leaving every vertex
of the distinguished original half unchanged. -/
def rightCliqueReindex {s t : ℕ}
    (p : Equiv.Perm (Fin s)) : CoverVertex s t ≃ CoverVertex s t where
  toFun x := (x.1, (if x.1 then p x.2.1 else x.2.1, x.2.2))
  invFun x := (x.1, (if x.1 then p.symm x.2.1 else x.2.1, x.2.2))
  left_inv := by
    rintro ⟨b,⟨i,a⟩⟩
    cases b <;> simp
  right_inv := by
    rintro ⟨b,⟨i,a⟩⟩
    cases b <;> simp

/-- Reindexing the outside half replaces mask(j) by mask(p(j)).
The internal clique graphs are preserved since p is a permutation. -/
theorem maskCoverGraph_comap_rightCliqueReindex {s t : ℕ}
    (mask : Fin s → Finset (Fin s))
    (p : Equiv.Perm (Fin s)) :
    (maskCoverGraph s t mask).comap (rightCliqueReindex p) =
      maskCoverGraph s t (fun j => mask (p j)) := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy <;>
    simp [rightCliqueReindex,maskCoverGraph,maskCoverAdj,
      Equiv.apply_eq_iff_eq,eq_comm,ne_comm]

/-- A family in any of the four normal forms is a uniform
generalized clique cover, after reindexing only the outside half.
The selected base embedding remains pointwise fixed. -/
theorem maskCoverGraph_four_forms_up_to_right_reindex {s t r : ℕ}
    (mask : Fin s → Finset (Fin s))
    (hForms :
      (r = 0 ∧ ∀ i : Fin s, mask i = ∅) ∨
      (r = 1 ∧ ∃ p : Equiv.Perm (Fin s),
        ∀ i : Fin s, mask (p i) = {i}) ∨
      (r + 1 = s ∧ ∃ p : Equiv.Perm (Fin s),
        ∀ i : Fin s, mask (p i) =
          (Finset.univ : Finset (Fin s)).erase i) ∨
      (r = s ∧ ∀ i : Fin s,
        mask i = (Finset.univ : Finset (Fin s)))) :
    ∃ (p : Equiv.Perm (Fin s)) (X : CrossType) (Y : Bool),
      (maskCoverGraph s t mask).comap (rightCliqueReindex p) =
        coverGraph s t X Y := by
  classical
  rcases hForms with ⟨_,hEmpty⟩ | ⟨_,p,hSing⟩ |
    ⟨_,p,hCo⟩ | ⟨_,hFull⟩
  · refine ⟨Equiv.refl _, .empty, false, ?_⟩
    rw [maskCoverGraph_comap_rightCliqueReindex]
    have hFunction :
        (fun i : Fin s => mask ((Equiv.refl _) i)) =
          (fun _ : Fin s => (∅ : Finset (Fin s))) := by
      funext i
      exact hEmpty i
    rw [hFunction]
    exact maskCoverGraph_empty_eq_coverGraph s t
  · refine ⟨p, .full, false, ?_⟩
    rw [maskCoverGraph_comap_rightCliqueReindex]
    have hFunction :
        (fun i : Fin s => mask (p i)) =
          (fun i : Fin s => ({i} : Finset (Fin s))) := by
      funext i
      exact hSing i
    rw [hFunction]
    exact maskCoverGraph_singleton_eq_coverGraph s t
  · refine ⟨p, .empty, true, ?_⟩
    rw [maskCoverGraph_comap_rightCliqueReindex]
    have hFunction :
        (fun i : Fin s => mask (p i)) =
          (fun i : Fin s => (Finset.univ : Finset (Fin s)).erase i) := by
      funext i
      exact hCo i
    rw [hFunction]
    exact maskCoverGraph_cosingleton_eq_coverGraph s t
  · refine ⟨Equiv.refl _, .full, true, ?_⟩
    rw [maskCoverGraph_comap_rightCliqueReindex]
    have hFunction :
        (fun i : Fin s => mask ((Equiv.refl _) i)) =
          (fun _ : Fin s => (Finset.univ : Finset (Fin s))) := by
      funext i
      exact hFull i
    rw [hFunction]
    exact maskCoverGraph_full_eq_coverGraph s t

end EPPAIII.CliqueCovers
