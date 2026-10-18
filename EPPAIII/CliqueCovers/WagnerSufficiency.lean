import EPPAIII.CliqueCovers.WagnerHostConclusion
import EPPAIII.EPPA.Definitions

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

def wagnerCycleEquiv : Fin 8 ≃ CoverVertex 2 2 :=
  Equiv.ofBijective wagnerCycleVertex wagnerCycleVertex_bijective

/-- Rotations and reflections modulo eight. -/
def wagnerIndexMap (a : Fin 8) (flip : Bool) (k : Fin 8) : Fin 8 :=
  if flip then a - k else a + k

theorem wagnerIndexMap_bijective (a : Fin 8) (flip : Bool) :
    Function.Bijective (wagnerIndexMap a flip) := by
  fin_cases a <;> cases flip <;> decide

def wagnerIndexPerm (a : Fin 8) (flip : Bool) : Equiv.Perm (Fin 8) :=
  Equiv.ofBijective (wagnerIndexMap a flip)
    (wagnerIndexMap_bijective a flip)

/-- A dihedral permutation transported along the cyclic labelling. -/
def wagnerSymmetry (a : Fin 8) (flip : Bool) :
    Equiv.Perm (CoverVertex 2 2) :=
  (wagnerCycleEquiv.symm.trans (wagnerIndexPerm a flip)).trans
    wagnerCycleEquiv

theorem wagnerSymmetry_graphAut :
    ∀ a : Fin 8, ∀ flip : Bool,
      IsGraphAutomorphism wagnerCanonicalGraph
        (wagnerSymmetry a flip) := by
  decide

/-- Exact sixteen-permutation certificate for all partial base
automorphisms of the designated two disjoint edges. -/
theorem wagner_partial_extends :
    ∀ (D : Finset (Fin 2 × Fin 2))
      (p : Equiv.Perm (Fin 2 × Fin 2)),
      IsPartialGraphAutomorphism (cliqueUnion 2 2) D p →
        ∃ a : Fin 8, ∃ flip : Bool, ∀ v : Fin 2 × Fin 2,
          v ∈ D →
          wagnerSymmetry a flip (coverLeftEmbedding 2 2 v) =
            coverLeftEmbedding 2 2 (p v) := by
  decide

theorem wagner_left_induced :
    IsInducedGraphEmbedding (cliqueUnion 2 2)
      wagnerCanonicalGraph (coverLeftEmbedding 2 2) := by
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
