import EPPAIII.Primitive.RankThreeCatalog
import EPPAIII.Primitive.Subconstituents
import EPPAIII.Primitive.CycleFiveCoverObstruction
import EPPAIII.CliqueCovers.TransitiveHalfEdges
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fin.VecNotation

/-! # Induced pentagons in both constituents of the order-120 model -/

namespace EPPAIII.Primitive

open scoped BigOperators

private def decode (mask : ℕ) : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) :=
  (fun i => if mask.testBit i.val then 1 else 0,
    fun i => if mask.testBit (i.val + 4) then 1 else 0)

private def checkedVertex (mask : ℕ) (h : (∑ i, (decode mask).1 i * (decode mask).2 i) = 1) :
    NonsingularOrthogonalEightVertex :=
  ⟨decode mask, h⟩

/-- The vector with value one in the first coordinate of each half. -/
def orthogonalEightRoot : NonsingularOrthogonalEightVertex := checkedVertex 17 (by decide)

private def localFive : Fin 5 → NonsingularOrthogonalEightVertex :=
  ![checkedVertex 35 (by decide), checkedVertex 54 (by decide),
    checkedVertex 43 (by decide), checkedVertex 197 (by decide), checkedVertex 139 (by decide)]

private def nonlocalFive : Fin 5 → NonsingularOrthogonalEightVertex :=
  ![checkedVertex 19 (by decide), checkedVertex 34 (by decide),
    checkedVertex 23 (by decide), checkedVertex 68 (by decide), checkedVertex 98 (by decide)]

private instance : DecidableRel nonsingularOrthogonalEightGraph.Adj := fun a b => by
  change Decidable (a ≠ b ∧ (∑ i, (a.val.1 i * b.val.2 i + b.val.1 i * a.val.2 i)) = 1)
  infer_instance

private theorem localFive_mem : ∀ i, nonsingularOrthogonalEightGraph.Adj orthogonalEightRoot (localFive i) := by
  decide

private theorem nonlocalFive_mem :
    ∀ i, orthogonalEightRoot ≠ nonlocalFive i ∧
      ¬ nonsingularOrthogonalEightGraph.Adj orthogonalEightRoot (nonlocalFive i) := by
  decide

private theorem localFive_injective : Function.Injective localFive := by decide
private theorem nonlocalFive_injective : Function.Injective nonlocalFive := by decide

private theorem localFive_adj :
    ∀ i j, nonsingularOrthogonalEightGraph.Adj (localFive i) (localFive j) ↔
      (SimpleGraph.cycleGraph 5).Adj i j := by
  decide

private theorem nonlocalFive_adj :
    ∀ i j, nonsingularOrthogonalEightGraph.Adj (nonlocalFive i) (nonlocalFive j) ↔
      (SimpleGraph.cycleGraph 5).Adj i j := by
  decide

/-- An induced pentagon in the 56-vertex neighbour graph. -/
def orthogonalEightLocalFiveCycle :
    SimpleGraph.cycleGraph 5 ↪g localGraph nonsingularOrthogonalEightGraph orthogonalEightRoot where
  toEmbedding := ⟨fun i => ⟨localFive i, localFive_mem i⟩,
    fun _ _ h => localFive_injective (congrArg Subtype.val h)⟩
  map_rel_iff' := fun {i j} => localFive_adj i j

/-- An induced pentagon in the 63-vertex nonneighbour graph. -/
def orthogonalEightNonlocalFiveCycle :
    SimpleGraph.cycleGraph 5 ↪g nonlocalGraph nonsingularOrthogonalEightGraph orthogonalEightRoot where
  toEmbedding := ⟨fun i => ⟨nonlocalFive i, nonlocalFive_mem i⟩,
    fun _ _ h => nonlocalFive_injective (congrArg Subtype.val h)⟩
  map_rel_iff' := fun {i j} => nonlocalFive_adj i j


/-- Either rooted constituent has an induced pentagon, once the host is
known to be transitive. The rank-three reduction supplies transitivity. -/
theorem orthogonalEight_fiveCycles_at_root
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms nonsingularOrthogonalEightGraph)
    (root : NonsingularOrthogonalEightVertex) :
    Nonempty (SimpleGraph.cycleGraph 5 ↪g localGraph nonsingularOrthogonalEightGraph root) ∧
      Nonempty (SimpleGraph.cycleGraph 5 ↪g nonlocalGraph nonsingularOrthogonalEightGraph root) := by
  let H := nonsingularOrthogonalEightGraph
  obtain ⟨q, hq, hRoot⟩ := hTrans orthogonalEightRoot root
  have hAdj (x : NonsingularOrthogonalEightVertex) :
      H.Adj orthogonalEightRoot x ↔ H.Adj root (q x) := by
    simpa only [hRoot] using hq orthogonalEightRoot x
  have hNonadj (x : NonsingularOrthogonalEightVertex) :
      (orthogonalEightRoot ≠ x ∧ ¬ H.Adj orthogonalEightRoot x) ↔
        (root ≠ q x ∧ ¬ H.Adj root (q x)) := by
    have hNe : orthogonalEightRoot ≠ x ↔ root ≠ q x := by
      rw [← hRoot]
      exact not_congr q.injective.eq_iff.symm
    exact and_congr hNe (hAdj x).not
  let localIso : localGraph H orthogonalEightRoot ≃g localGraph H root :=
    ⟨q.subtypeEquiv hAdj, fun {a b} => (hq a b).symm⟩
  let nonlocalIso : nonlocalGraph H orthogonalEightRoot ≃g nonlocalGraph H root :=
    ⟨q.subtypeEquiv hNonadj, fun {a b} => (hq a b).symm⟩
  exact ⟨⟨localIso.toEmbedding.comp orthogonalEightLocalFiveCycle⟩,
    ⟨nonlocalIso.toEmbedding.comp orthogonalEightNonlocalFiveCycle⟩⟩


/-- The four forms remaining for a constituent after the reductions in
Section 8. -/
def HasCliqueUnionOrCoverModel {V : Type*} (G : SimpleGraph V) : Prop :=
  (∃ s t, IsModelUpToComplement G (cliqueUnion s t)) ∨
    (∃ s t X Y, IsModelUpToComplement G (coverGraph s t X Y))

/-- None of the four constituent forms contain an induced five-cycle. -/
theorem not_cliqueUnionOrCover_of_fiveCycle {V : Type*} {G : SimpleGraph V}
    (f : SimpleGraph.cycleGraph 5 ↪g G) : ¬ HasCliqueUnionOrCoverModel G := by
  rintro (⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩)
  · rcases h with h | h
    · obtain ⟨φ⟩ := h
      exact (no_clique_union_or_compl_of_induced_five_cycle f s t).1.false φ
    · obtain ⟨φ⟩ := h
      exact (no_clique_union_or_compl_of_induced_five_cycle f s t).2.false φ
  · rcases h with h | h
    · obtain ⟨φ⟩ := h
      exact (no_cover_or_compl_of_induced_five_cycle f s t X Y).1.false φ
    · obtain ⟨φ⟩ := h
      exact (no_cover_or_compl_of_induced_five_cycle f s t X Y).2.false φ

/-- The order-120 nonsingular orthogonal graph cannot meet the Section 8
constituent-shape requirement at any vertex. -/
theorem orthogonalEight_constituents_exclude_forms
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms nonsingularOrthogonalEightGraph)
    (root : NonsingularOrthogonalEightVertex) :
    ¬ HasCliqueUnionOrCoverModel (localGraph nonsingularOrthogonalEightGraph root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph nonsingularOrthogonalEightGraph root) := by
  obtain ⟨⟨f⟩, ⟨g⟩⟩ := orthogonalEight_fiveCycles_at_root hTrans root
  exact ⟨not_cliqueUnionOrCover_of_fiveCycle f, not_cliqueUnionOrCover_of_fiveCycle g⟩

end EPPAIII.Primitive
