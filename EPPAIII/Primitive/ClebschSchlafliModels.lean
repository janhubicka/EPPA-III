import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Powerset

/-!
# Clebsch and Schläfli models in the finite witnesses list

The masks use the vertex labels from the finite computations. Only maximal
orbit representatives at or above half of the host order are listed.
-/

namespace EPPAIII.Primitive

private def clebschConnection (a b : Fin 16) : Prop :=
  Nat.xor a.val b.val ∈ ([1, 2, 4, 8, 15] : List Nat)

private instance : DecidableRel clebschConnection :=
  fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List Nat)))

/-- The Clebsch Cayley graph with the binary labels used in the certificate. -/
def clebschGraph : SimpleGraph (Fin 16) where
  Adj := clebschConnection
  symm := ⟨by
    have h : ∀ a b : Fin 16, clebschConnection a b → clebschConnection b a := by
      decide
    exact h⟩
  loopless := ⟨by decide⟩

instance : DecidableRel clebschGraph.Adj :=
  inferInstanceAs (DecidableRel clebschConnection)

private def schlafliPairs : List (Finset Nat) :=
  [{0, 1}, {0, 2}, {0, 3}, {0, 4}, {0, 5}, {1, 2}, {1, 3}, {1, 4}, {1, 5},
    {2, 3}, {2, 4}, {2, 5}, {3, 4}, {3, 5}, {4, 5}]

private def schlafliPair (a : Fin 27) : Finset Nat :=
  schlafliPairs[a.val - 12]?.getD ∅

private def schlafliSkew (a b : Fin 27) : Prop :=
  a ≠ b ∧
    if a.val < 12 then
      if b.val < 12 then a.val / 6 = b.val / 6 ∨ a.val % 6 = b.val % 6
      else a.val % 6 ∉ schlafliPair b
    else
      if b.val < 12 then b.val % 6 ∉ schlafliPair a
      else (schlafliPair a ∩ schlafliPair b).card = 1

private instance : DecidableRel schlafliSkew :=
  fun a b => by
    unfold schlafliSkew
    infer_instance

set_option maxRecDepth 20000 in
/-- The Schläfli graph on the double-six labels. Indices 0–5 and 6–11
index the two sixes. Indices 12–26 index the pairs in lexicographic order. -/
def schlafliGraph : SimpleGraph (Fin 27) where
  Adj := schlafliSkew
  symm := ⟨by
    have h : ∀ a b : Fin 27, schlafliSkew a b → schlafliSkew b a := by
      decide
    exact h⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel schlafliGraph.Adj :=
  inferInstanceAs (DecidableRel schlafliSkew)

/-- The finite vertex selection whose indices are set in the given mask. -/
def maskVertices (n : Nat) (mask : Nat) : Set (Fin n) :=
  {a | mask.testBit a.val = true}

/-- The five large Clebsch maximal selections in the finite certificate. -/
def clebschLargeFigures : Set (Set (Fin 16)) :=
  maskVertices 16 '' {mask | mask ∈ ([0xff, 0x33f, 0x3cf, 0x777, 0x177e] : List Nat)}

/-- The fourteen large Schläfli maximal selections in the finite certificate. -/
def schlafliLargeFigures : Set (Set (Fin 27)) :=
  maskVertices 27 '' {mask | mask ∈ ([63455, 419823, 440295, 452589, 517997, 976863,
    976892, 1042300, 2092860, 2803679, 2803687, 3072988, 7164891, 16630264] : List Nat)}

end EPPAIII.Primitive
