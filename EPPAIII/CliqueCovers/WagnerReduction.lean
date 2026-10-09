import EPPAIII.EPPA.Definitions

/-!
# Excluding the cube from the Wagner reduction

This verifies the short EPPA obstruction for the all-matching 2x2
connection matrix. The chosen base is the first 2K₂, and a transposition
within its second K₂ cannot be extended to the cube: it changes the
existence of a common neighbour with a fixed vertex in the first K₂.

There is no enumeration of the automorphism group and no unproved axiom.
-/

namespace EPPAIII

/-- The graph with four matching blocks, a three-dimensional cube. -/
def cubeMatchingAdj (x y : CoverVertex 2 2) : Prop :=
  (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 ≠ y.1 ∧ x.2.2 = y.2.2)

def cubeMatchingGraph : SimpleGraph (CoverVertex 2 2) where
  Adj := cubeMatchingAdj
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hs, hi, ha⟩ | ⟨hs, ha⟩
    · exact Or.inl ⟨hs.symm, hi.symm, ha.symm⟩
    · exact Or.inr ⟨hs.symm, ha.symm⟩
  loopless := by
    constructor
    intro x h
    rcases h with ⟨_, _, ha⟩ | ⟨hs, _⟩
    · exact ha rfl
    · exact hs rfl

/-- The designated first half of the cube is an induced 2K₂. -/
theorem cubeMatching_left_induced :
    IsInducedGraphEmbedding (cliqueUnion 2 2) cubeMatchingGraph
      (coverLeftEmbedding 2 2) := by
  intro u v
  rcases u with ⟨i, a⟩
  rcases v with ⟨j, b⟩
  simp [cliqueUnion, cubeMatchingGraph, cubeMatchingAdj, coverLeftEmbedding]

/-- Swapping the two vertices of the second clique is a (total)
partial automorphism of the designated first half. -/
private def swapSecond : Equiv.Perm (Fin 2 × Fin 2) :=
  Equiv.swap ((1 : Fin 2), (0 : Fin 2)) ((1 : Fin 2), (1 : Fin 2))

private theorem swapSecond_partial :
    IsPartialGraphAutomorphism (cliqueUnion 2 2) Finset.univ swapSecond := by
  decide

/-- A vertex in the first clique and the first vertex in the second
clique have a common neighbour in the opposite half. -/
private theorem common_for_first :
    cubeMatchingGraph.Adj (left (0 : Fin 2) (0 : Fin 2))
      (right (0 : Fin 2) (0 : Fin 2)) ∧
    cubeMatchingGraph.Adj (left (1 : Fin 2) (0 : Fin 2))
      (right (0 : Fin 2) (0 : Fin 2)) := by
  decide

/-- But replacing the second-clique vertex by its mate destroys
all common neighbours. This is a concrete graph invariant. -/
private theorem no_common_for_second :
    ∀ w : CoverVertex 2 2,
      ¬ (cubeMatchingGraph.Adj (left (0 : Fin 2) (0 : Fin 2)) w ∧
         cubeMatchingGraph.Adj (left (1 : Fin 2) (1 : Fin 2)) w) := by
  decide

/-- The cube is not an EPPA witness for the designated 2K₂.
This replaces the computational exclusion in the last paragraph of
the proof of Claim 3.11. -/
theorem cubeMatching_not_EPPA :
    ¬ IsEPPAEmbedding (cliqueUnion 2 2) cubeMatchingGraph
        (coverLeftEmbedding 2 2) := by
  intro hEPPA
  obtain ⟨q, hq, hExt⟩ :=
    hEPPA.2 Finset.univ swapSecond swapSecond_partial
  have hFix : q (left (0 : Fin 2) (0 : Fin 2)) =
      left (0 : Fin 2) (0 : Fin 2) := by
    simpa [coverLeftEmbedding, swapSecond] using
      (hExt ((0 : Fin 2), (0 : Fin 2)) (Finset.mem_univ _))
  have hSwap : q (left (1 : Fin 2) (0 : Fin 2)) =
      left (1 : Fin 2) (1 : Fin 2) := by
    simpa [coverLeftEmbedding, swapSecond] using
      (hExt ((1 : Fin 2), (0 : Fin 2)) (Finset.mem_univ _))
  have h₁ := (hq (left (0 : Fin 2) (0 : Fin 2))
    (right (0 : Fin 2) (0 : Fin 2))).mp common_for_first.1
  have h₂ := (hq (left (1 : Fin 2) (0 : Fin 2))
    (right (0 : Fin 2) (0 : Fin 2))).mp common_for_first.2
  exact no_common_for_second (q (right (0 : Fin 2) (0 : Fin 2)))
    ⟨hFix ▸ h₁, hSwap ▸ h₂⟩

end EPPAIII
