import EPPAIII.BlockSystems.RookThreeFourSubsetOrbits

/-!
# The two size-nine orbits on four-subsets of R3

The orbit of the four-neighbour pattern contains precisely
the nine open neighbourhoods of the 3×3 rook graph.
The other size-nine orbit contains precisely the nine
sets of four distinct nonneighbours of each base vertex.

Both identifications are checked as exact finite-set
equalities by kernel reduction. The two labelling maps
are injective, so either orbit gives canonical labels
by the nine original rook vertices. This is the finite
classification input to the degree-four case in Lemma 3.20,
separate from the yet-to-be-verified adjacency of the outside half.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

/-- Four neighbours in the distinguished 3×3 rook graph. -/
def rookOpenNeighbourhood (x : rookVertex) : Finset rookVertex :=
  (Finset.univ : Finset rookVertex).filter
    (fun y => rookThreeGraph.Adj x y)

/-- Four distinct nonneighbours of x in the rook graph. -/
def rookStrictNonneighbours (x : rookVertex) : Finset rookVertex :=
  (Finset.univ : Finset rookVertex).filter
    (fun y => y ≠ x ∧ ¬ rookThreeGraph.Adj x y)

theorem rook_open_neighbourhood_card :
    ∀ x : rookVertex, (rookOpenNeighbourhood x).card = 4 := by
  decide

theorem rook_strict_nonneighbours_card :
    ∀ x : rookVertex, (rookStrictNonneighbours x).card = 4 := by
  decide

/-- The two-disjoint-edges representative of the size-nine orbit
is exactly the neighbour set of one rook vertex. -/
theorem rook_nine_orbit_eq_neighbourhoods :
    rookSubsetOrbit rookFourNineOther =
      (Finset.univ : Finset rookVertex).image
        rookOpenNeighbourhood := by
  decide

/-- The four-cycle representative of the other size-nine orbit
is exactly the strict nonneighbour set of one rook vertex. -/
theorem rook_other_nine_orbit_eq_nonneighbourhoods :
    rookSubsetOrbit rookFourSquare =
      (Finset.univ : Finset rookVertex).image
        rookStrictNonneighbours := by
  decide

/-- A rook vertex is determined by its four neighbours. -/
theorem rook_open_neighbourhood_injective :
    Function.Injective rookOpenNeighbourhood := by
  decide

/-- A rook vertex is also determined by its four nonneighbours. -/
theorem rook_strict_nonneighbours_injective :
    Function.Injective rookStrictNonneighbours := by
  decide

end EPPAIII.BlockSystems
