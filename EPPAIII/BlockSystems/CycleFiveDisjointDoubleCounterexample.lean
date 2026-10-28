import EPPAIII.BlockSystems.DisjointDoubleInvariantBlocks
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.Fintype.Perm

/-!
# The omitted 2C5 host in Proposition 6.17

The five-cycle is homogeneous. We certify this independently
using its ten explicit dihedral automorphisms and a finite
decidable check of all partial automorphisms. The base is
connected and has a three-vertex induced path.

Consequently its two-copy disjoint union is an EPPA witness
for the original five-cycle, vertex-transitive, genuinely
imprimitive, and not homogeneous. Hence it cannot be dropped
from the final classification under the pretext of host
homogeneity.

The positive homogeneity check concerns just five vertices,
not an arbitrary-order family or an external classification.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Rotations and reflections of five cyclic vertex labels. -/
def cycleFiveDihedralMap (r : Fin 5) (flip : Bool)
    (x : Fin 5) : Fin 5 :=
  if flip then r - x else r + x

/-- Each of the ten dihedral actions is a bijection. -/
def cycleFiveDihedralPerm (r : Fin 5) (flip : Bool) :
    Equiv.Perm (Fin 5) where
  toFun := cycleFiveDihedralMap r flip
  invFun := fun x => if flip then r - x else x - r
  left_inv := by
    fin_cases r <;> cases flip <;> decide
  right_inv := by
    fin_cases r <;> cases flip <;> decide

/-- All ten dihedral permutations preserve the five-cycle. -/
theorem cycleFiveDihedral_graphAut :
    ∀ r : Fin 5, ∀ flip : Bool,
      EPPAIII.IsGraphAutomorphism (SimpleGraph.cycleGraph 5)
        (cycleFiveDihedralPerm r flip) := by
  change ∀ r : Fin 5, ∀ flip : Bool, ∀ x y : Fin 5,
    (SimpleGraph.cycleGraph 5).Adj x y ↔
      (SimpleGraph.cycleGraph 5).Adj
        (cycleFiveDihedralPerm r flip x)
        (cycleFiveDihedralPerm r flip y)
  decide

/-- Exhaustive finite certificate: each partial automorphism
of C5 agrees on its finite domain with one of the ten
dihedral symmetries. The assertion is only about the finite
base and carries no classification hypothesis. -/
theorem cycleFiveDihedral_extends_partial :
    ∀ (D : Finset (Fin 5)) (p : Equiv.Perm (Fin 5)),
      EPPAIII.IsPartialGraphAutomorphism
        (SimpleGraph.cycleGraph 5) D p →
      ∃ (r : Fin 5) (flip : Bool),
        ∀ x : Fin 5, x ∈ D →
          cycleFiveDihedralPerm r flip x = p x := by
  letI : Fintype (Equiv.Perm (Fin 5)) := Equiv.instFintype
  decide

/-- The five-cycle is homogeneous, witnessed by its explicit
dihedral automorphisms. -/
theorem cycleFive_isHomogeneous :
    EPPAIII.DoubleCover.IsHomogeneousGraph
      (SimpleGraph.cycleGraph 5) := by
  intro D p hp
  obtain ⟨r,flip,hExt⟩ :=
    cycleFiveDihedral_extends_partial D p hp
  exact ⟨cycleFiveDihedralPerm r flip,
    cycleFiveDihedral_graphAut r flip,hExt⟩

/-- The five-cycle has a genuine induced path on 0,1,2. -/
theorem cycleFive_inducedP3 :
    (SimpleGraph.cycleGraph 5).Adj 0 1 ∧
    (SimpleGraph.cycleGraph 5).Adj 1 2 ∧
    (0 : Fin 5) ≠ 2 ∧
    ¬ (SimpleGraph.cycleGraph 5).Adj 0 2 := by
  decide

/-- Fully explicit omitted example: 2C5 has all
hypotheses of the nonhomogeneous imprimitive EPPA-host
part of Proposition 6.17. -/
theorem cycleFive_disjoint_double_imprimitive_counterexample :
    EPPAIII.IsEPPAEmbedding (SimpleGraph.cycleGraph 5)
      (disjointDoubleGraph (SimpleGraph.cycleGraph 5))
      (EPPAIII.DoubleCover.bottomEmbedding (Fin 5)) ∧
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (disjointDoubleGraph (SimpleGraph.cycleGraph 5)) ∧
    ¬ EPPAIII.DoubleCover.IsHomogeneousGraph
      (disjointDoubleGraph (SimpleGraph.cycleGraph 5)) ∧
    InvariantBlockMap (disjointDoubleGraph (SimpleGraph.cycleGraph 5))
      (fun w : Bool × Fin 5 => w.1) ∧
    Function.Surjective (fun w : Bool × Fin 5 => w.1) ∧
    (∃ side : Bool, 2 ≤
      ((Finset.univ : Finset (Bool × Fin 5)).filter
        (fun w => w.1 = side)).card) := by
  obtain ⟨hab,hbc,hac,hnot⟩ := cycleFive_inducedP3
  exact disjoint_double_imprimitive_counterexample_schema
    (SimpleGraph.cycleGraph 5) cycleFive_isHomogeneous
    (by
      first
      | exact SimpleGraph.cycleGraph_preconnected
      | exact SimpleGraph.preconnected_cycleGraph)
    0 1 2 hab hbc hac hnot

end EPPAIII.BlockSystems
