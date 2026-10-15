import EPPAIII.DoubleCover.TaylorLayerSum

/-!
# Reduce the four Boolean triangle layers to three counts

For any graph on Bool × V, reversing the ordered pair of
non-root vertices swaps the (false,true) and (true,false)
layers bijectively. The ordered triangle count is therefore
the two same-layer counts plus twice the mixed-layer count.

This is independent of Taylor's matrix pattern or EPPA.
-/

namespace EPPAIII.DoubleCover

theorem taylor_triangle_layer_card_swap {V : Type*}
    [Fintype V]
    (H : SimpleGraph (Bool × V))
    (x : V) (a b : Bool) :
    (taylorTriangleLayerPairs H x a b).card =
      (taylorTriangleLayerPairs H x b a).card := by
  classical
  refine Finset.card_bij'
    (fun yz _ => (yz.2,yz.1))
    (fun yz _ => (yz.2,yz.1)) ?_ ?_ ?_ ?_
  · intro yz hyz
    obtain ⟨h1,h2,h3⟩ :=
      (mem_taylorTriangleLayerPairs H x a b yz.1 yz.2).mp hyz
    exact (mem_taylorTriangleLayerPairs
      H x b a yz.2 yz.1).mpr ⟨h2,h1,h3.symm⟩
  · intro yz hyz
    obtain ⟨h1,h2,h3⟩ :=
      (mem_taylorTriangleLayerPairs H x b a yz.1 yz.2).mp hyz
    exact (mem_taylorTriangleLayerPairs
      H x a b yz.2 yz.1).mpr ⟨h2,h1,h3.symm⟩
  · intro yz hyz
    rcases yz with ⟨y,z⟩
    rfl
  · intro yz hyz
    rcases yz with ⟨y,z⟩
    rfl

/-- The four terms in the abstract Bool×Bool sum. -/
theorem ordered_triangle_pairs_card_four_layers {V : Type*}
    [Fintype V]
    (H : SimpleGraph (Bool × V))
    (x : V) :
    (orderedTrianglePairsAt H (false,x)).card =
      (taylorTriangleLayerPairs H x false false).card +
      (taylorTriangleLayerPairs H x false true).card +
      (taylorTriangleLayerPairs H x true false).card +
      (taylorTriangleLayerPairs H x true true).card := by
  rw [ordered_triangle_pairs_card_sum_layers H x]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  omega

/-- Only three separate layer cardinalities need to be counted:
both mixed orientations make the same contribution. -/
theorem ordered_triangle_pairs_card_three_layers {V : Type*}
    [Fintype V]
    (H : SimpleGraph (Bool × V))
    (x : V) :
    (orderedTrianglePairsAt H (false,x)).card =
      (taylorTriangleLayerPairs H x false false).card +
      2 * (taylorTriangleLayerPairs H x false true).card +
      (taylorTriangleLayerPairs H x true true).card := by
  have hFour := ordered_triangle_pairs_card_four_layers H x
  have hSwap := taylor_triangle_layer_card_swap H x true false
  omega

end EPPAIII.DoubleCover
