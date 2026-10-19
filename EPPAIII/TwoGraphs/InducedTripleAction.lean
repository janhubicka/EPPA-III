import EPPAIII.DoubleCover.InducedTwoTransitiveAssembly
import EPPAIII.TwoGraphs.TaylorFibresDistance

/-!
# The triangle two-graph induced from a Taylor double

A base triple is declared present when its three associated natural
fibres admit a triangle in the Taylor double. This is an intrinsic,
switching-invariant definition. Any automorphism of the Taylor graph
that preserves its fibre system must preserve this triple relation.

An identification with the usual odd-edge-parity definition of a
two-graph is proved separately in the following parity module.
-/

namespace EPPAIII.TwoGraphs

/-- Intrinsic triple relation: there is a triangle with one point
from each of the three fibres. -/
def TaylorTriple (G : SimpleGraph V) (x y z : V) : Prop :=
  ∃ b c d : Bool,
    (taylorPairGraph G).Adj (b,x) (c,y) ∧
    (taylorPairGraph G).Adj (c,y) (d,z) ∧
    (taylorPairGraph G).Adj (d,z) (b,x)

/-- Transport a triple's chosen triangle through a genuine
fibre-preserving automorphism of the Taylor double. -/
theorem taylorTriple_transport_forward
    {V : Type*} (G : SimpleGraph V)
    (A : EPPAIII.DoubleCover.InducedFibreAut (taylorPairGraph G))
    (x y z : V) :
    TaylorTriple G x y z →
      TaylorTriple G (A.σ x) (A.σ y) (A.σ z) := by
  rintro ⟨b,c,d,hbc,hcd,hdb⟩
  refine ⟨(A.q (b,x)).1, (A.q (c,y)).1,
    (A.q (d,z)).1, ?_, ?_, ?_⟩
  · have h := (A.hAut (b,x) (c,y)).mp hbc
    simpa only [← A.hBase b x, ← A.hBase c y, Prod.eta] using h
  · have h := (A.hAut (c,y) (d,z)).mp hcd
    simpa only [← A.hBase c y, ← A.hBase d z, Prod.eta] using h
  · have h := (A.hAut (d,z) (b,x)).mp hdb
    simpa only [← A.hBase d z, ← A.hBase b x, Prod.eta] using h

/-- Exact preservation by the induced action on base fibres.
No EPPA or transitivity is needed once the fibre action exists. -/
theorem taylorTriple_preserved_by_induced_action
    {V : Type*} (G : SimpleGraph V)
    (A : EPPAIII.DoubleCover.InducedFibreAut (taylorPairGraph G))
    (x y z : V) :
    TaylorTriple G x y z ↔
      TaylorTriple G (A.σ x) (A.σ y) (A.σ z) := by
  constructor
  · exact taylorTriple_transport_forward G A x y z
  · intro h
    have hBack := taylorTriple_transport_forward
      G A.inverse (A.σ x) (A.σ y) (A.σ z) h
    simpa using hBack

end EPPAIII.TwoGraphs
