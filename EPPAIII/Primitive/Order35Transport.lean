import EPPAIII.Primitive.BinaryOrthogonalModels
import EPPAIII.Primitive.EqualBipartitionModels
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Powerset

/-!
# The two order-35 models

The graph of four-subset bipartitions is the complement of split-quadric
perpendicularity. The finite certificate uses a Witt basis in the quotient
of even subsets of eight points by complementation.
-/

namespace EPPAIII.Primitive

open BlockSystems.BinaryFiveCycles

private def order35BasisMask (i : Nat) : Nat :=
  match i with
  | 0 => 30
  | 1 => 114
  | 2 => 184
  | 3 => 46
  | 4 => 116
  | _ => 198

private def order35Part (x : Fin 64) : Finset (Fin 8) :=
  Finset.univ.filter fun i =>
    bit ((List.range 6).foldl
      (fun mask j => if bit x.val j = 1 then Nat.xor mask (order35BasisMask j) else mask)
      255) i.val = 1

set_option maxRecDepth 30000 in
private theorem order35Part_valid :
    ∀ x : OrthogonalSixVertex true true, (order35Part x.val).card = 4 ∧
      (0 : Fin 8) ∈ order35Part x.val := by
  decide

private def order35Vertex (x : OrthogonalSixVertex true true) : EqualBipartitionVertex 3 :=
  ⟨order35Part x.val, order35Part_valid x⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem order35Part_injective :
    ∀ a b : OrthogonalSixVertex true true,
      order35Part a.val = order35Part b.val → a = b := by
  decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem order35_card :
    Fintype.card (OrthogonalSixVertex true true) =
      Fintype.card (EqualBipartitionVertex 3) := by
  decide

private theorem order35Vertex_bijective : Function.Bijective order35Vertex := by
  have hinj : Function.Injective order35Vertex := fun a b h =>
    order35Part_injective a b (congrArg Subtype.val h)
  exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, order35_card⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem order35_adjacency :
    ∀ a b : OrthogonalSixVertex true true,
      (a ≠ b ∧ ¬ (a ≠ b ∧ polarPlus a.val.val b.val.val = 0)) ↔
        (order35Vertex a ≠ order35Vertex b ∧
          (((order35Part a.val ∩ order35Part b.val).card = 1) ∨
           ((order35Part a.val ∩ order35Part b.val).card = 3))) := by
  decide

/-- The degree-16 bipartition graph is the complement of the degree-18
perpendicularity graph on nonzero singular vectors. -/
noncomputable def order35OrthogonalComplementIso :
    (orthogonalSixGraph true true)ᶜ ≃g equalBipartitionGraph 3 where
  toEquiv := Equiv.ofBijective order35Vertex order35Vertex_bijective
  map_rel_iff' := by
    intro a b
    exact (order35_adjacency a b).symm

end EPPAIII.Primitive
