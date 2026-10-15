import EPPAIII.DoubleCover.TaylorLayerBasePairs

/-!
# Every triangle pair is counted in exactly one Boolean layer

For an arbitrary finite graph on Bool × V, the two Boolean
coordinates of an ordered triangle pair give a partition into
four layer types. Forgetting those two fixed coordinates is a
bijection with the corresponding finite set of base pairs.

This is the purely finite-counting bridge between the actual
ordered triangle count and the layer-set equalities proved for
Taylor doubles. No Taylor pattern assumption is used here.
-/

namespace EPPAIII.DoubleCover

/-- The fibre of actual ordered triangle pairs with prescribed
Boolean layers is in bijection with its projected base-pair set. -/
theorem ordered_triangle_layer_fibre_card {V : Type*}
    [Fintype V]
    (H : SimpleGraph (Bool × V)) (x : V) (a b : Bool) :
    ((orderedTrianglePairsAt H (false,x)).filter
      (fun p => (p.1.1,p.2.1) = (a,b))).card =
        (taylorTriangleLayerPairs H x a b).card := by
  classical
  refine Finset.card_bij'
    (fun p _ => (p.1.2,p.2.2))
    (fun yz _ => ((a,yz.1),(b,yz.2))) ?_ ?_ ?_ ?_
  · intro p hp
    have hPair := (Finset.mem_filter.mp hp).1
    have hAB := (Finset.mem_filter.mp hp).2
    have ha : p.1.1 = a := congrArg Prod.fst hAB
    have hb : p.2.1 = b := congrArg Prod.snd hAB
    have hTriangle :
        H.Adj (false,x) p.1 ∧
        H.Adj (false,x) p.2 ∧ H.Adj p.1 p.2 := by
      simpa [orderedTrianglePairsAt] using hPair
    apply (mem_taylorTriangleLayerPairs
      H x a b p.1.2 p.2.2).mpr
    simpa only [← ha, ← hb] using hTriangle
  · intro yz hyz
    have hTriangle :=
      (mem_taylorTriangleLayerPairs H x a b yz.1 yz.2).mp hyz
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl⟩
    simpa [orderedTrianglePairsAt] using hTriangle
  · intro p hp
    have hAB := (Finset.mem_filter.mp hp).2
    rcases p with ⟨⟨c,y⟩,⟨d,z⟩⟩
    have hc : c = a := congrArg Prod.fst hAB
    have hd : d = b := congrArg Prod.snd hAB
    subst c
    subst d
    rfl
  · intro yz hyz
    rcases yz with ⟨y,z⟩
    rfl

/-- The actual ordered triangle count at the bottom root is
the sum of its four disjoint Boolean-layer counts. -/
theorem ordered_triangle_pairs_card_sum_layers {V : Type*}
    [Fintype V]
    (H : SimpleGraph (Bool × V)) (x : V) :
    (orderedTrianglePairsAt H (false,x)).card =
      ∑ ab : Bool × Bool,
        (taylorTriangleLayerPairs H x ab.1 ab.2).card := by
  classical
  let f : ((Bool × V) × (Bool × V)) → Bool × Bool :=
    fun p => (p.1.1,p.2.1)
  have hGroup :
      (orderedTrianglePairsAt H (false,x)).card =
        ∑ ab : Bool × Bool,
          ((orderedTrianglePairsAt H (false,x)).filter
            (fun p => f p = ab)).card := by
    simpa only [f] using
      (Finset.card_eq_sum_card_fiberwise
        (s := orderedTrianglePairsAt H (false,x))
        (t := (Finset.univ : Finset (Bool × Bool)))
        (f := f)
        (by intro p hp; exact Finset.mem_univ _))
  calc
    (orderedTrianglePairsAt H (false,x)).card =
        ∑ ab : Bool × Bool,
          ((orderedTrianglePairsAt H (false,x)).filter
            (fun p => f p = ab)).card := hGroup
    _ = ∑ ab : Bool × Bool,
          (taylorTriangleLayerPairs H x ab.1 ab.2).card := by
      apply Finset.sum_congr rfl
      intro ab _
      rcases ab with ⟨a,b⟩
      exact ordered_triangle_layer_fibre_card H x a b

end EPPAIII.DoubleCover
