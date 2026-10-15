import EPPAIII.BlockSystems.RookThreeSubsetAction

/-!
# Certified small-subset orbits of the nine-vertex rook graph

Under the explicit 72 automorphisms from RookThreeSubsetAction,
the 2-subsets split into two orbits of size 18.
The 3-subsets split into four orbits, of sizes 6, 6, 36, 36.

We prove exact orbit cardinalities and exhaustiveness by
finite kernel reduction using Lean decide on explicit sets,
not by Python enumeration or an abstract group-action claim.
Since the action consists of genuine graph automorphisms,
these orbit sizes constrain invariant outside profiles.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192

abbrev rookVertex : Type := Fin 3 × Fin 3

/-- Representative of an adjacent pair in one row. -/
def rookTwoAdjacent : Finset rookVertex :=
  {(0,0),(0,1)}

/-- Representative of a nonadjacent pair. -/
def rookTwoNonadjacent : Finset rookVertex :=
  {(0,0),(1,1)}

/-- A 3-clique: three vertices in one row. -/
def rookThreeClique : Finset rookVertex :=
  {(0,0),(0,1),(0,2)}

/-- An independent triple: one point in each row and column. -/
def rookThreeIndependent : Finset rookVertex :=
  {(0,0),(1,1),(2,2)}

/-- A right-angle triple with two rook edges. -/
def rookThreeCorner : Finset rookVertex :=
  {(0,0),(0,1),(1,0)}

/-- A triple containing just one rook edge. -/
def rookThreeSingleEdge : Finset rookVertex :=
  {(0,0),(0,1),(1,2)}

theorem rookTwoAdjacent_orbit_card :
    (rookSubsetOrbit rookTwoAdjacent).card = 18 := by
  decide

theorem rookTwoNonadjacent_orbit_card :
    (rookSubsetOrbit rookTwoNonadjacent).card = 18 := by
  decide

theorem rookThreeClique_orbit_card :
    (rookSubsetOrbit rookThreeClique).card = 6 := by
  decide

theorem rookThreeIndependent_orbit_card :
    (rookSubsetOrbit rookThreeIndependent).card = 6 := by
  decide

theorem rookThreeCorner_orbit_card :
    (rookSubsetOrbit rookThreeCorner).card = 36 := by
  decide

theorem rookThreeSingleEdge_orbit_card :
    (rookSubsetOrbit rookThreeSingleEdge).card = 36 := by
  decide

/-- Every two-element subset belongs to one of the two orbits. -/
theorem rook_two_subsets_orbit_partition :
    ((Finset.univ : Finset rookVertex).powersetCard 2) =
      rookSubsetOrbit rookTwoAdjacent ∪
        rookSubsetOrbit rookTwoNonadjacent := by
  decide

/-- The four orbits exhaust all three-element subsets. -/
theorem rook_three_subsets_orbit_partition :
    ((Finset.univ : Finset rookVertex).powersetCard 3) =
      rookSubsetOrbit rookThreeClique ∪
        rookSubsetOrbit rookThreeIndependent ∪
        rookSubsetOrbit rookThreeCorner ∪
        rookSubsetOrbit rookThreeSingleEdge := by
  decide

end EPPAIII.BlockSystems
