import EPPAIII.CliqueCovers.CoSingletonChoiceLabels
import EPPAIII.CliqueCovers.WreathProfileEquivariance

/-!
# Wreath-equivariance of co-singleton profile choices

The natural imprimitive action on co-singleton choices records the
unique OMITTED point. A permutation of an individual clique sends
the complement of {a} to the complement of {p a}, and outer
permutations move the unique selected clique index.

This is the precise combinatorial input for the co-singleton
one-partial case in the direct Section 3 argument.
-/

namespace EPPAIII.CliqueCovers

/-- Mapping a co-singleton through a permutation maps the omitted
point by that same permutation. -/
theorem perm_map_compl_singleton {t : ℕ}
    (p : Equiv.Perm (Fin t)) (a : Fin t) :
    (({a} : Finset (Fin t))ᶜ).map p.toEmbedding =
      (({p a} : Finset (Fin t))ᶜ) := by
  classical
  ext b
  simp only [Finset.mem_map, Finset.mem_compl, Finset.mem_singleton]
  constructor
  · rintro ⟨z, hza, hzb⟩
    intro hba
    apply hza
    exact p.injective (hzb.trans hba)
  · intro hba
    refine ⟨p.symm b, ?_, p.apply_symm_apply b⟩
    intro hza
    apply hba
    exact (p.apply_symm_apply b).symm.trans (congrArg p hza)

/-- A single selected co-singleton coordinate determines its
extracted choice by its index and omitted point. -/
theorem extractKChoice_eq_coSingletonChoice {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (i : Fin s) (a : Fin t)
    (hPositions : kPositions P (t - 1) = {i})
    (hSlice : profileSlice P i = (({a} : Finset (Fin t))ᶜ)) :
    extractKChoice P (t - 1) =
      (coSingletonChoiceOfPair (i,a)).val := by
  classical
  change
    (⟨kPositions P (t - 1), fun j _ => profileSlice P j⟩ :
      Σ R : Finset (Fin s), ∀ j : Fin s, j ∈ R → Finset (Fin t)) =
    ⟨{i}, fun _j _hj => (({a} : Finset (Fin t))ᶜ)⟩
  rw [hPositions]
  congr 1
  funext j hj
  have hji : j = i := by simpa using hj
  subst j
  exact hSlice

/-- Exact natural wreath transformation of co-singleton labels:
the index is outer(i), and the omitted point is
inner_(outer(i))(a). -/
theorem extractKChoice_wreath_coSingleton {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (i : Fin s) (a : Fin t)
    (hPositions : kPositions P (t - 1) = {i})
    (hSlice : profileSlice P i = (({a} : Finset (Fin t))ᶜ))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t)) :
    extractKChoice (wreathTransform P outer inner) (t - 1) =
      (coSingletonChoiceOfPair
        (((outerPermutation outer).trans
          (innerPermutation inner)) (i,a))).val := by
  classical
  have hPositions' :
      kPositions (wreathTransform P outer inner) (t - 1) =
        {outer i} := by
    rw [kPositions_wreathTransform, hPositions]
    simp
  have hSlice' :
      profileSlice (wreathTransform P outer inner) (outer i) =
        (({inner (outer i) a} : Finset (Fin t))ᶜ) := by
    rw [profileSlice_wreathTransform]
    simpa [hSlice] using
      (perm_map_compl_singleton (inner (outer i)) a)
  have hExtract := extractKChoice_eq_coSingletonChoice
    (wreathTransform P outer inner)
    (outer i) (inner (outer i) a) hPositions' hSlice'
  simpa [outerPermutation, innerPermutation] using hExtract

end EPPAIII.CliqueCovers
