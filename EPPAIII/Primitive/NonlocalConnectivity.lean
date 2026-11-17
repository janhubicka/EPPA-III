import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Card

namespace EPPAIII.Primitive

/-- If a strongly regular graph has positive nonedge codegree and more
distinct nonneighbors than its degree, its second subconstituent is connected.
Vertices in different components would have the same set of neighbors
in the first subconstituent, forcing a common neighbor of the entire second. -/
theorem nonlocalGraph_connected_of_degree_lt_order
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {n k l μ : ℕ} (hSRG : H.IsSRGWith n k l μ) (hμ : 0 < μ) (r : V)
    (hSize : k < Nat.card {x : V // r ≠ x ∧ ¬ H.Adj r x}) :
    (nonlocalGraph H r).Connected := by
  classical
  let U := {x : V // r ≠ x ∧ ¬ H.Adj r x}
  let J := nonlocalGraph H r
  have hU : Nonempty U := (Nat.card_pos_iff.mp (Nat.zero_lt_of_lt hSize)).1
  change J.Connected
  refine @SimpleGraph.Connected.mk U J ?_ hU
  intro a b
  by_contra hAB
  have equalToLocal (u v : U) (hUV : ¬ J.Reachable u v) :
      H.commonNeighbors u.val v.val = H.commonNeighbors r u.val := by
    have hNe : u.val ≠ v.val := fun e => hUV (Subtype.ext e ▸ SimpleGraph.Reachable.rfl)
    have hAdj : ¬ H.Adj u.val v.val := fun h => hUV (show J.Adj u v from h).reachable
    have hSubset (z : H.commonNeighbors u.val v.val) :
        z.val ∈ H.commonNeighbors r u.val := by
      obtain ⟨huz, hvz⟩ := H.mem_commonNeighbors.mp z.property
      refine H.mem_commonNeighbors.mpr ⟨?_, huz⟩
      by_contra hNot
      have hrz : r ≠ z.val := by
        intro e
        exact u.property.2 ((congrArg (fun x : V => H.Adj x u.val) e).mpr huz.symm)
      let w : U := ⟨z.val, hrz, hNot⟩
      exact hUV ((show J.Adj u w from huz).reachable.trans
        (show J.Adj w v from hvz.symm).reachable)
    let f : H.commonNeighbors u.val v.val → H.commonNeighbors r u.val :=
      fun x => ⟨x.val, hSubset x⟩
    have hSurj : Function.Surjective f := by
      by_contra hn
      have hLt := Fintype.card_lt_of_injective_not_surjective f
        (fun _ _ h => Subtype.ext (congrArg (fun x : H.commonNeighbors r u.val => x.val) h)) hn
      rw [hSRG.of_not_adj hNe hAdj, hSRG.of_not_adj u.property.1 u.property.2] at hLt
      exact (Nat.lt_irrefl μ) hLt
    ext z
    refine ⟨fun hz => hSubset ⟨z, hz⟩, fun hz => ?_⟩
    obtain ⟨w, hw⟩ := hSurj ⟨z, hz⟩
    have hv : w.val = z := congrArg Subtype.val hw
    exact hv ▸ w.property
  have equalLocal (u v : U) (hUV : ¬ J.Reachable u v) :
      H.commonNeighbors r u.val = H.commonNeighbors r v.val := by
    exact (equalToLocal u v hUV).symm.trans
      ((H.commonNeighbors_symm _ _).trans (equalToLocal v u (fun h => hUV h.symm)))
  have hPos : 0 < Fintype.card (H.commonNeighbors r a.val) := by
    rw [hSRG.of_not_adj a.property.1 a.property.2]
    exact hμ
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hPos
  have hAll (u : U) : H.Adj z.val u.val := by
    have hEq : H.commonNeighbors r a.val = H.commonNeighbors r u.val := by
      by_cases hu : J.Reachable a u
      · exact (equalLocal a b hAB).trans (equalLocal u b (fun h => hAB (hu.trans h))).symm
      · exact equalLocal a u hu
    have huz : z.val ∈ H.commonNeighbors r u.val := hEq ▸ z.property
    exact (H.mem_commonNeighbors.mp huz).2.symm
  let g : U → H.neighborSet z.val := fun u => ⟨u.val, hAll u⟩
  have hBound := Nat.card_le_card_of_injective g (fun _ _ h =>
    Subtype.ext (congrArg (fun x : H.neighborSet z.val => x.val) h))
  have hDegree : Nat.card (H.neighborSet z.val) = k := by
    rw [Nat.card_eq_fintype_card, H.card_neighborSet_eq_degree, hSRG.regular z.val]
  rw [hDegree] at hBound
  exact (not_le_of_gt hSize) hBound

end EPPAIII.Primitive
