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

/-- Rotations act transitively on the five vertices.
The finite certificate avoids invoking any group classification. -/
theorem cycleFive_rotations_transitive (x y : Fin 5) :
    ∃ r : Fin 5, cycleFiveDihedralPerm r false x = y := by
  fin_cases x <;> fin_cases y <;> decide

/-- The dihedral action is transitive on ordered edges and
on ordered nonedges. These are just 5⁴ finite cases. -/
theorem cycleFive_ordered_pair_transitive :
    ∀ x y u v : Fin 5,
      x ≠ y → u ≠ v →
      ((SimpleGraph.cycleGraph 5).Adj x y ↔
       (SimpleGraph.cycleGraph 5).Adj u v) →
      ∃ r : Fin 5, ∃ flip : Bool,
        cycleFiveDihedralPerm r flip x = u ∧
        cycleFiveDihedralPerm r flip y = v := by
  decide

/-- Once two different anchors are prescribed, the adjacency
pattern to them distinguishes all *other* C5 vertices. -/
theorem cycleFive_two_anchor_types_injective :
    ∀ a b z w : Fin 5,
      a ≠ b → z ≠ a → z ≠ b → w ≠ a → w ≠ b →
      ((SimpleGraph.cycleGraph 5).Adj a z ↔
       (SimpleGraph.cycleGraph 5).Adj a w) →
      ((SimpleGraph.cycleGraph 5).Adj b z ↔
       (SimpleGraph.cycleGraph 5).Adj b w) →
      z = w := by
  decide

/-- Every partial automorphism of C5 extends to an explicit
dihedral symmetry. This is a mathematical two-anchor proof,
rather than enumeration of all 32 domains and 120 permutations. -/
theorem cycleFiveDihedral_extends_partial :
    ∀ (D : Finset (Fin 5)) (p : Equiv.Perm (Fin 5)),
      EPPAIII.IsPartialGraphAutomorphism
        (SimpleGraph.cycleGraph 5) D p →
      ∃ (r : Fin 5) (flip : Bool),
        ∀ x : Fin 5, x ∈ D →
          cycleFiveDihedralPerm r flip x = p x := by
  classical
  intro D p hp
  let G := SimpleGraph.cycleGraph 5
  by_cases hLarge : 1 < D.card
  · obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp hLarge
    obtain ⟨r,flip,hxMap,hyMap⟩ :=
      cycleFive_ordered_pair_transitive
        x y (p x) (p y) hxy (p.injective.ne hxy)
        (hp x y hx hy)
    let q : Equiv.Perm (Fin 5) := cycleFiveDihedralPerm r flip
    have hq : EPPAIII.IsGraphAutomorphism G q :=
      cycleFiveDihedral_graphAut r flip
    refine ⟨r,flip,?_⟩
    intro z hz
    change q z = p z
    by_cases hzx : z = x
    · subst z
      exact hxMap
    by_cases hzy : z = y
    · subst z
      exact hyMap
    have hqzx : q z ≠ p x := by
      intro h
      exact hzx (q.injective (h.trans hxMap.symm))
    have hqzy : q z ≠ p y := by
      intro h
      exact hzy (q.injective (h.trans hyMap.symm))
    have hpzx : p z ≠ p x := p.injective.ne hzx
    have hpzy : p z ≠ p y := p.injective.ne hzy
    have hTypeX : G.Adj (p x) (q z) ↔ G.Adj (p x) (p z) := by
      calc
        G.Adj (p x) (q z) ↔ G.Adj x z := by
          simpa only [hxMap] using (hq x z).symm
        _ ↔ G.Adj (p x) (p z) := hp x z hx hz
    have hTypeY : G.Adj (p y) (q z) ↔ G.Adj (p y) (p z) := by
      calc
        G.Adj (p y) (q z) ↔ G.Adj y z := by
          simpa only [hyMap] using (hq y z).symm
        _ ↔ G.Adj (p y) (p z) := hp y z hy hz
    exact cycleFive_two_anchor_types_injective
      (p x) (p y) (q z) (p z)
      (p.injective.ne hxy) hqzx hqzy hpzx hpzy hTypeX hTypeY
  · by_cases hSome : D.Nonempty
    · obtain ⟨x,hx⟩ := hSome
      have hSmall : D.card ≤ 1 := by omega
      have hUnique (z : Fin 5) (hz : z ∈ D) : z = x :=
        (Finset.card_le_one_iff.mp hSmall) hz hx
      obtain ⟨r,hRx⟩ := cycleFive_rotations_transitive x (p x)
      refine ⟨r,false,?_⟩
      intro z hz
      rw [hUnique z hz]
      exact hRx
    · refine ⟨0,false,?_⟩
      intro z hz
      exact (hSome ⟨z,hz⟩).elim

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
    (by exact SimpleGraph.cycleGraph_preconnected)
    0 1 2 hab hbc hac hnot

end EPPAIII.BlockSystems
