import EPPAIII.CliqueCovers.Claim39OrbitBridge

/-!
# Exact coordinate equivariance under a lifted wreath automorphism

The existing EPPA transport lemma identifies the *whole* finite
neighbourhood profile of q(u) with the image of the profile of u under
the base automorphism p.  For a wreath automorphism this means:
* the set of size-k coordinate positions is carried by the outer
  permutation, and
* the slice at index i is obtained by first taking the old slice at
  outer⁻¹(i), then applying the corresponding inner permutation.

These identities hold for every vertex u and every compatible graph
automorphism q, not only for a chosen representative, and need no
coherent system of extensions or outside-clique decomposition.

They supply the actual EPPA-to-natural-action bridge used in the
one-partial and Wagner graph-transport arguments of Section 3.
-/

namespace EPPAIII.CliqueCovers

/-- The slice at index i of a wreath-transformed profile is exactly
the transformed slice at the inverse outer index. -/
theorem profileSlice_wreathTransform {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (i : Fin s) :
    profileSlice (wreathTransform P outer inner) i =
      (profileSlice P (outer.symm i)).map (inner i).toEmbedding := by
  classical
  unfold wreathTransform
  rw [profileSlice_inner, profileSlice_outer]

/-- The selected size-k index set is transported by the outer
permutation (inner coordinate maps preserve cardinality). -/
theorem kPositions_wreathTransform {s t : ℕ}
    (P : Finset (Fin s × Fin t))
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (k : ℕ) :
    kPositions (wreathTransform P outer inner) k =
      (kPositions P k).map outer.toEmbedding := by
  classical
  unfold wreathTransform
  rw [kPositions_inner, kPositions_outer_map]

/-- The actual profile of a vertex moved by an EPPA lift agrees
with the concrete wreath transformation of its original profile.
Only graph-automorphism and base-compatibility assumptions are used. -/
theorem finite_profile_wreath_lift {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (u : W)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hCompat : ∀ v : Fin s × Fin t,
      q (e v) =
        e (((outerPermutation outer).trans
          (innerPermutation inner)) v)) :
    finiteNeighbourhoodProfile H e (q u) =
      wreathTransform (finiteNeighbourhoodProfile H e u) outer inner := by
  let p : Equiv.Perm (Fin s × Fin t) :=
    (outerPermutation outer).trans (innerPermutation inner)
  calc
    finiteNeighbourhoodProfile H e (q u) =
        translatedFiniteProfile H e u p :=
      finite_profile_transport H e u p q hCompat hq
    _ = (finiteNeighbourhoodProfile H e u).map p.toEmbedding :=
      translatedFiniteProfile_eq_map H e u p
    _ = wreathTransform (finiteNeighbourhoodProfile H e u)
        outer inner :=
      (wreathTransform_eq_map
        (finiteNeighbourhoodProfile H e u) outer inner).symm

/-- Actual neighbourhood slices transform by the specified outer
and inner permutations of the distinguished clique union. -/
theorem profileSlice_of_wreath_lift {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (u : W)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hCompat : ∀ v : Fin s × Fin t,
      q (e v) =
        e (((outerPermutation outer).trans
          (innerPermutation inner)) v))
    (i : Fin s) :
    profileSlice (finiteNeighbourhoodProfile H e (q u)) i =
      (profileSlice (finiteNeighbourhoodProfile H e u)
        (outer.symm i)).map (inner i).toEmbedding := by
  rw [finite_profile_wreath_lift H e u outer inner q hq hCompat]
  exact profileSlice_wreathTransform
    (finiteNeighbourhoodProfile H e u) outer inner i

/-- The actual set of size-k coordinate indices is carried exactly
by the outer permutation of the base clique indices. -/
theorem kPositions_of_wreath_lift {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (u : W)
    (outer : Equiv.Perm (Fin s))
    (inner : Fin s → Equiv.Perm (Fin t))
    (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hCompat : ∀ v : Fin s × Fin t,
      q (e v) =
        e (((outerPermutation outer).trans
          (innerPermutation inner)) v))
    (k : ℕ) :
    kPositions (finiteNeighbourhoodProfile H e (q u)) k =
      (kPositions (finiteNeighbourhoodProfile H e u) k).map
        outer.toEmbedding := by
  rw [finite_profile_wreath_lift H e u outer inner q hq hCompat]
  exact kPositions_wreathTransform
    (finiteNeighbourhoodProfile H e u) outer inner k

end EPPAIII.CliqueCovers
