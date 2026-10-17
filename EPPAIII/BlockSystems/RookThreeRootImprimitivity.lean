import EPPAIII.BlockSystems.RookThreeSmallSubsetOrbits

/-!
# A finite obstruction to nontrivial rook imprimitivity blocks

Fix the rook vertex (0,0). The subgroup stabilizing it acts with
two orbits of size four on the other eight vertices. In particular
there is no invariant three-vertex subset containing the root.

The proof uses just three explicit generators: interchange rows
1 and 2, interchange columns 1 and 2, and transpose. An exhaustive
512-subset finite check proves the claimed obstruction, independently
of any host graph and without a classification theorem.

This is the delicate finite ingredient in current Claim 6.15.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

private def rookFixRow : rookAutParameter := (3,0,false)
private def rookFixColumn : rookAutParameter := (0,3,false)
private def rookFixTranspose : rookAutParameter := (0,0,true)

theorem rook_root_generators_fix_root :
    rookParameterizedAut rookFixRow (0,0) = (0,0) ∧
    rookParameterizedAut rookFixColumn (0,0) = (0,0) ∧
    rookParameterizedAut rookFixTranspose (0,0) = (0,0) := by
  decide

/-- Invariant sets of the rooted rook action cannot have three points:
the only possibilities have cardinality 1, 5, or 9. The concrete
certificate uses the three displayed root-stabilizer generators. -/
theorem rook_root_invariant_subset_not_three
    (S : Finset rookVertex) (hRoot : (0,0) ∈ S)
    (hInv : ∀ p : rookAutParameter,
      rookParameterizedAut p (0,0) = (0,0) →
        S.image (rookParameterizedAut p) = S) :
    S.card ≠ 3 := by
  have hFinite :
      ∀ T : Finset rookVertex,
        (0,0) ∈ T →
        T.image (rookParameterizedAut rookFixRow) = T →
        T.image (rookParameterizedAut rookFixColumn) = T →
        T.image (rookParameterizedAut rookFixTranspose) = T →
        T.card ≠ 3 := by
    decide
  obtain ⟨hRow,hCol,hTranspose⟩ :=
    rook_root_generators_fix_root
  exact hFinite S hRoot
    (hInv rookFixRow hRow)
    (hInv rookFixColumn hCol)
    (hInv rookFixTranspose hTranspose)

end EPPAIII.BlockSystems
