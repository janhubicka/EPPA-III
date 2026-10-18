import EPPAIII.BlockSystems.RookThreeDoubleAdjacency
import EPPAIII.BlockSystems.CycleFiveDoubleClassification

/-!
# Named patterns of the exceptional C5 and R3 doubles

The exceptional classifications construct actual finite adjacency
models. This module checks their identification with the named
Taylor double and the complement of a two-clique extension.
For the five-cycle one reindexes only the upper half.
All finite adjacency calculations are kernel-checked.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- The rook-nonedge cross relation has exactly Taylor adjacency. -/
theorem rook_double_nonneighbour_is_taylor :
    ∀ u v : Bool × rookVertex,
      (rookDoubleGraph false true).Adj u v ↔
        (if u.1 = v.1 then rookThreeGraph.Adj u.2 v.2
         else u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2) := by
  decide

/-- The other rook double is the mate-free two-fold blow-up. -/
theorem rook_double_neighbour_is_matefree_blowup :
    ∀ u v : Bool × rookVertex,
      (rookDoubleGraph false false).Adj u v ↔
        rookThreeGraph.Adj u.2 v.2 := by
  decide

/-- This blow-up is the complement of the two-clique extension
of the complementary rook graph. Self-complementarity of R3
gives the paper's named two-clique-extension model. -/
theorem rook_matefree_is_complement_of_anti_rook_extension :
    ∀ u v : Bool × rookVertex,
      rookThreeGraph.Adj u.2 v.2 ↔
        (u ≠ v ∧ ¬
          (u.2 = v.2 ∨ rookThreeGraphᶜ.Adj u.2 v.2)) := by
  decide

/-- Shift just the upper five-cycle indices by d. -/
def cycleFiveUpperShift (d : Fin 5) (u : Bool × Fin 5) :
    Bool × Fin 5 :=
  (u.1, if u.1 then u.2 + d else u.2)

/-- The shift is a bijection fixing all lower cycle vertices. -/
theorem cycleFiveUpperShift_bijective :
    ∀ d : Fin 5, Function.Bijective (cycleFiveUpperShift d) := by
  decide

/-- Adjacent-pair profiles give the Taylor double after
shifting upper indices by three. -/
theorem cycleFive_adjacent_pair_double_is_taylor :
    ∀ u v : Bool × Fin 5,
      (cycleFiveDoubleGraph false false).Adj u v ↔
        (let u' := cycleFiveUpperShift 3 u
         let v' := cycleFiveUpperShift 3 v
         if u'.1 = v'.1 then cycleFiveExplicitAdjacent u'.2 v'.2
         else u'.2 ≠ v'.2 ∧ ¬ cycleFiveExplicitAdjacent u'.2 v'.2) := by
  decide

/-- Diagonal-pair profiles give the mate-free blow-up after
shifting upper indices by one. -/
theorem cycleFive_diagonal_pair_double_is_matefree_blowup :
    ∀ u v : Bool × Fin 5,
      (cycleFiveDoubleGraph false true).Adj u v ↔
        cycleFiveExplicitAdjacent
          (cycleFiveUpperShift 1 u).2
          (cycleFiveUpperShift 1 v).2 := by
  decide

/-- For C5 the mate-free blow-up is the complement of the
two-clique extension of the complementary five-cycle. -/
theorem cycleFive_matefree_is_complement_extension :
    ∀ u v : Bool × Fin 5,
      cycleFiveExplicitAdjacent u.2 v.2 ↔
        (u ≠ v ∧ ¬
          (u.2 = v.2 ∨
             (SimpleGraph.cycleGraph 5)ᶜ.Adj u.2 v.2)) := by
  decide

end EPPAIII.BlockSystems
