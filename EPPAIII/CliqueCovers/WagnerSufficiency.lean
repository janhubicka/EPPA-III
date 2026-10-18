import EPPAIII.CliqueCovers.WagnerHostConclusion
import EPPAIII.EPPA.Definitions
import EPPAIII.CliqueCovers.CliqueUnionHomogeneity

/-!
# The Wagner graph is an EPPA witness for the selected 2K₂

The necessary-side profile theorem identifies the exceptional host
with an explicit eight-vertex Möbius ladder. To certify sufficiency,
we use sixteen symmetries of its Hamiltonian eight-cycle and its
antipodal chords. The finite statement is kernel-checked.
-/

namespace EPPAIII.CliqueCovers

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- A computable adjacency decision for the finite canonical graph. -/
private instance : DecidableRel wagnerCanonicalGraph.Adj := by
  intro u v
  change Decidable (wagnerCanonicalAdj u v)
  unfold wagnerCanonicalAdj
  infer_instance

/-- Computable base adjacency on the designated two disjoint edges. -/
private instance : DecidableRel (cliqueUnion 2 2).Adj := by
  intro u v
  change Decidable (u.1 = v.1 ∧ u.2 ≠ v.2)
  infer_instance

/-- Enumerate the Wagner Möbius ladder in cyclic order. -/
def wagnerCycleVertex (k : Fin 8) : CoverVertex 2 2 :=
  match k.val with
  | 0 => (false, (0, 0))
  | 1 => (true, (0, 0))
  | 2 => (false, (1, 0))
  | 3 => (true, (1, 0))
  | 4 => (false, (0, 1))
  | 5 => (true, (1, 1))
  | 6 => (false, (1, 1))
  | _ => (true, (0, 1))

theorem wagnerCycleVertex_bijective :
    Function.Bijective wagnerCycleVertex := by
  decide

/-- Explicit inverse labelling, so all certificates compute by reduction. -/
def wagnerCycleIndex (u : CoverVertex 2 2) : Fin 8 :=
  if u = (false, (0, 0)) then 0
  else if u = (true, (0, 0)) then 1
  else if u = (false, (1, 0)) then 2
  else if u = (true, (1, 0)) then 3
  else if u = (false, (0, 1)) then 4
  else if u = (true, (1, 1)) then 5
  else if u = (false, (1, 1)) then 6
  else 7

def wagnerCycleEquiv : Fin 8 ≃ CoverVertex 2 2 where
  toFun := wagnerCycleVertex
  invFun := wagnerCycleIndex
  left_inv := by decide
  right_inv := by decide

/-- Rotations and reflections modulo eight. -/
def wagnerIndexMap (a : Fin 8) (flip : Bool) (k : Fin 8) : Fin 8 :=
  if flip then a - k else a + k

theorem wagnerIndexMap_bijective (a : Fin 8) (flip : Bool) :
    Function.Bijective (wagnerIndexMap a flip) := by
  fin_cases a <;> cases flip <;> decide

def wagnerIndexPerm (a : Fin 8) (flip : Bool) : Equiv.Perm (Fin 8) where
  toFun := wagnerIndexMap a flip
  invFun := fun k => if flip then a - k else k - a
  left_inv := by
    fin_cases a <;> cases flip <;> decide
  right_inv := by
    fin_cases a <;> cases flip <;> decide

/-- A dihedral permutation transported along the cyclic labelling. -/
def wagnerSymmetry (a : Fin 8) (flip : Bool) :
    Equiv.Perm (CoverVertex 2 2) :=
  (wagnerCycleEquiv.symm.trans (wagnerIndexPerm a flip)).trans
    wagnerCycleEquiv

theorem wagnerSymmetry_graphAut :
    ∀ a : Fin 8, ∀ flip : Bool,
      IsGraphAutomorphism wagnerCanonicalGraph
        (wagnerSymmetry a flip) := by
  change ∀ a : Fin 8, ∀ flip : Bool, ∀ u v : CoverVertex 2 2,
    wagnerCanonicalAdj u v ↔
      wagnerCanonicalAdj (wagnerSymmetry a flip u)
        (wagnerSymmetry a flip v)
  letI : DecidableRel wagnerCanonicalAdj := by
    intro u v
    unfold wagnerCanonicalAdj
    infer_instance
  decide

/-- Fully computational certificate over the 256 maps of four points.
We avoid attempting to enumerate equivalence structures directly:
injectivity and adjacency preservation are checked as explicit
finite predicates on an ordinary function. -/
theorem wagner_full_function_extension :
    ∀ f : (Fin 2 × Fin 2) → (Fin 2 × Fin 2),
      (∀ u v : Fin 2 × Fin 2, f u = f v → u = v) →
      (∀ u v : Fin 2 × Fin 2,
        (u.1 = v.1 ∧ u.2 ≠ v.2) ↔
          ((f u).1 = (f v).1 ∧ (f u).2 ≠ (f v).2)) →
      ∃ a : Fin 8, ∃ flip : Bool, ∀ v : Fin 2 × Fin 2,
        wagnerSymmetry a flip (false,v) = (false,f v) := by
  decide

/-- Any partial base automorphism first extends inside the
homogeneous two-clique base and then extends via a Wagner symmetry.
The only finite exhaustive step concerns full maps of four points. -/
theorem wagner_partial_extends :
    ∀ (D : Finset (Fin 2 × Fin 2))
      (p : Equiv.Perm (Fin 2 × Fin 2)),
      IsPartialGraphAutomorphism (cliqueUnion 2 2) D p →
        ∃ a : Fin 8, ∃ flip : Bool, ∀ v : Fin 2 × Fin 2,
          v ∈ D →
          wagnerSymmetry a flip (coverLeftEmbedding 2 2 v) =
            coverLeftEmbedding 2 2 (p v) := by
  intro D p hp
  obtain ⟨sigma, hAut, hAgree⟩ :=
    cliqueUnion_isHomogeneous 2 2 D p hp
  have hAdj (u v : Fin 2 × Fin 2) :
      (u.1 = v.1 ∧ u.2 ≠ v.2) ↔
        ((sigma u).1 = (sigma v).1 ∧
          (sigma u).2 ≠ (sigma v).2) := hAut u v
  obtain ⟨a,flip,hAll⟩ :=
    wagner_full_function_extension sigma sigma.injective hAdj
  refine ⟨a,flip,?_⟩
  intro v hv
  change wagnerSymmetry a flip (false,v) = (false,p v)
  calc
    wagnerSymmetry a flip (false,v) = (false,sigma v) := hAll v
    _ = (false,p v) :=
      congrArg (fun z => (false,z)) (hAgree v hv)

theorem wagner_left_induced :
    IsInducedGraphEmbedding (cliqueUnion 2 2)
      wagnerCanonicalGraph (coverLeftEmbedding 2 2) := by
  change ∀ u v : Fin 2 × Fin 2,
    (u.1 = v.1 ∧ u.2 ≠ v.2) ↔
      wagnerCanonicalAdj (false,u) (false,v)
  letI : DecidableRel wagnerCanonicalAdj := by
    intro u v
    unfold wagnerCanonicalAdj
    infer_instance
  decide

/-- The exceptional Wagner graph itself is an EPPA witness. -/
theorem wagnerCanonicalGraph_isEPPA :
    IsEPPAEmbedding (cliqueUnion 2 2)
      wagnerCanonicalGraph (coverLeftEmbedding 2 2) := by
  refine ⟨wagner_left_induced, ?_⟩
  intro D p hp
  obtain ⟨a, flip, hExt⟩ := wagner_partial_extends D p hp
  exact ⟨wagnerSymmetry a flip,
    wagnerSymmetry_graphAut a flip, hExt⟩

end EPPAIII.CliqueCovers
