import EPPAIII.EPPA.InducedSubsetEPPA

/-!
# Minimal EPPA obstructions inside a fixed finite host

An EPPA obstacle is an actual selected vertex subset B of H such that
H fails EPPA for B, but succeeds for every proper selected subset.
Since EPPA on subsets is downward-closed, every failing subset
contains a minimal failing subset. This yields the precise
obstruction-hypergraph avoidance criterion.

This theorem is independent of the classification of obstacles for
particular host families; it uses only finite subset induction and
the previously formalized hereditary EPPA property.
-/

namespace EPPAIII

/-- Inclusion-minimal failure of EPPA for a particular induced
vertex subset of the host (not an abstract graph isomorphism type). -/
def IsMinimalEPPAObstruction {V : Type*}
    (H : SimpleGraph V) (B : Finset V) : Prop :=
  ¬ IsEPPAOnSubset H B ∧
    ∀ T : Finset V, T ⊂ B → IsEPPAOnSubset H T

/-- Every non-EPPA selected vertex subset contains an inclusion-minimal
non-EPPA selected subset. No ambient transitivity is assumed. -/
theorem non_eppa_contains_minimal_obstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V)
    (hBad : ¬ IsEPPAOnSubset H S) :
    ∃ B : Finset V, B ⊆ S ∧ IsMinimalEPPAObstruction H B := by
  classical
  have hAll (U : Finset V) :
      (¬ IsEPPAOnSubset H U) →
        ∃ B : Finset V, B ⊆ U ∧ IsMinimalEPPAObstruction H B := by
    apply Finset.strongInductionOn U
    intro U ih hU
    by_cases hMinimal :
        ∀ T : Finset V, T ⊂ U → IsEPPAOnSubset H T
    · exact ⟨U, Finset.Subset.rfl, hU, hMinimal⟩
    · push_neg at hMinimal
      obtain ⟨T,hTU,hTbad⟩ := hMinimal
      obtain ⟨B,hBT,hBmin⟩ := ih T hTU hTbad
      have hTsub : T ⊆ U := (Finset.ssubset_def.mp hTU).1
      exact ⟨B,hBT.trans hTsub,hBmin⟩
  exact hAll S hBad

/-- The exact logical characterization of all admissible EPPA subsets:
an induced vertex subset has EPPA iff it contains no minimal obstacle. -/
theorem eppa_iff_avoids_minimal_obstructions
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Finset V) :
    IsEPPAOnSubset H S ↔
      ∀ B : Finset V, IsMinimalEPPAObstruction H B → ¬ B ⊆ S := by
  constructor
  · intro hGood B hMin hSub
    exact hMin.1 (eppa_on_subset_downward H hSub hGood)
  · intro hAvoid
    by_contra hBad
    obtain ⟨B,hBS,hMin⟩ :=
      non_eppa_contains_minimal_obstruction H S hBad
    exact (hAvoid B hMin) hBS

end EPPAIII
