import EPPAIII.TwoGraphs.InducedTripleAction

/-!
# Taylor triangles are exactly odd triples of the base switching class

A three-fibre triangle in the canonical Taylor double exists if and
only if the three base edges have odd parity. This gives a direct
elementary identification with the usual two-graph of the base G
and upgrades the intrinsic-triple preservation theorem to its standard
odd-parity formulation.
-/

namespace EPPAIII.TwoGraphs

/-- Odd edge parity of the three distinct base vertices. -/
def OddBaseTriple {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y z : V) : Prop :=
  Bool.xor (Bool.xor (decide (G.Adj x y))
    (decide (G.Adj y z))) (decide (G.Adj z x)) = true

/-- A triangle can be assigned three fibre-side bits precisely
when the parity of the three relations is odd. -/
theorem boolean_triangle_iff_odd (a b c : Bool) :
    (∃ i j k : Bool,
      (a = true ↔ i = j) ∧
      (b = true ↔ j = k) ∧
      (c = true ↔ k = i)) ↔
        Bool.xor (Bool.xor a b) c = true := by
  cases a <;> cases b <;> cases c <;> decide

/-- The intrinsic Taylor triple relation agrees with the original
odd-edge-parity two-graph on sets of three distinct points. -/
theorem taylorTriple_iff_odd
    {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y z : V)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    TaylorTriple G x y z ↔ OddBaseTriple G x y z := by
  classical
  change (∃ b c d : Bool,
    (x ≠ y ∧ (G.Adj x y ↔ b = c)) ∧
    (y ≠ z ∧ (G.Adj y z ↔ c = d)) ∧
    (z ≠ x ∧ (G.Adj z x ↔ d = b))) ↔
    Bool.xor (Bool.xor (decide (G.Adj x y))
      (decide (G.Adj y z))) (decide (G.Adj z x)) = true
  simp [hxy, hyz, hzx]
  simpa only [decide_eq_true_eq] using
    boolean_triangle_iff_odd
      (decide (G.Adj x y))
      (decide (G.Adj y z))
      (decide (G.Adj z x))

/-- Under a fibre-preserving automorphism of the Taylor double,
the induced base automorphism preserves the ordinary odd triple
relation of the associated two-graph. -/
theorem oddBaseTriple_preserved_by_induced_action
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : EPPAIII.DoubleCover.InducedFibreAut (taylorPairGraph G))
    (x y z : V)
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    OddBaseTriple G x y z ↔
      OddBaseTriple G (A.σ x) (A.σ y) (A.σ z) := by
  exact (taylorTriple_iff_odd G x y z hxy hyz hzx).symm.trans
    ((taylorTriple_preserved_by_induced_action G A x y z).trans
      (taylorTriple_iff_odd G (A.σ x) (A.σ y) (A.σ z)
        (A.σ.injective.ne hxy)
        (A.σ.injective.ne hyz)
        (A.σ.injective.ne hzx)))

end EPPAIII.TwoGraphs
