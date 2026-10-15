import EPPAIII.BlockSystems.RookThreeSmallSubsetOrbits

/-!
# Four-vertex rook graph subset orbits

The 126 four-element subsets of the nine-vertex rook graph
split under the explicit 72 row/column/transpose automorphisms
into two orbits of size nine and three orbits of size 36.

Each orbit representative and its finite cardinality is stated
explicitly. The exhaustiveness certificate is computed by Lean
kernel reduction, not by an external script or unverified table.
These are the remaining orbit sizes used in Lemma 3.20.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

/-- The four vertices of a 2×2 rook square. -/
def rookFourSquare : Finset rookVertex :=
  {(0,0),(0,1),(1,0),(1,1)}

/-- Two rook edges arranged in opposite rows and columns. -/
def rookFourNineOther : Finset rookVertex :=
  {(0,0),(0,1),(1,2),(2,2)}

/-- A complete row with one additional adjacent vertex. -/
def rookFourLinePlus : Finset rookVertex :=
  {(0,0),(0,1),(0,2),(1,0)}

/-- A corner and a fourth vertex in the same outer row. -/
def rookFourCornerPlus : Finset rookVertex :=
  {(0,0),(0,1),(1,0),(1,2)}

/-- A corner and a diagonally placed fourth vertex. -/
def rookFourCornerDiagonal : Finset rookVertex :=
  {(0,0),(0,1),(1,0),(2,2)}

theorem rookFourSquare_orbit_card :
    (rookSubsetOrbit rookFourSquare).card = 9 := by
  decide

theorem rookFourNineOther_orbit_card :
    (rookSubsetOrbit rookFourNineOther).card = 9 := by
  decide

theorem rookFourLinePlus_orbit_card :
    (rookSubsetOrbit rookFourLinePlus).card = 36 := by
  decide

theorem rookFourCornerPlus_orbit_card :
    (rookSubsetOrbit rookFourCornerPlus).card = 36 := by
  decide

theorem rookFourCornerDiagonal_orbit_card :
    (rookSubsetOrbit rookFourCornerDiagonal).card = 36 := by
  decide

/-- The five indicated orbits exhaust all 126 four-element subsets. -/
theorem rook_four_subsets_orbit_partition :
    ((Finset.univ : Finset rookVertex).powersetCard 4) =
      rookSubsetOrbit rookFourSquare ∪
        rookSubsetOrbit rookFourNineOther ∪
        rookSubsetOrbit rookFourLinePlus ∪
        rookSubsetOrbit rookFourCornerPlus ∪
        rookSubsetOrbit rookFourCornerDiagonal := by
  decide

end EPPAIII.BlockSystems
