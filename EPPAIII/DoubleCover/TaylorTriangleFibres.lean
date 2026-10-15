import EPPAIII.DoubleCover.TaylorMateTriangles
import EPPAIII.DoubleCover.TriangleTransport

/-!
# Taylor triangles never repeat a base fibre

The optional mate edge inside any fibre cannot lie in a triangle.
More precisely, a triangle through the bottom vertex (false,x)
cannot use the mate (true,x), nor can its other two vertices
belong to the same base fibre. These statements follow from
the already validated Taylor inter-fibre pattern, without any
hypothesis about the mate matching.

We also introduce the actual ordered triangle pairs with fixed
Boolean layers of the two non-root vertices. Their four cardinalities
will be identified with finite combinatorial sets of base vertices.
-/

namespace EPPAIII.DoubleCover

/-- Both other vertices of a Taylor triangle through (false,x)
have base coordinates different from x. -/
theorem taylor_triangle_avoids_root_fibre {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x : V) (u v : Bool × V)
    (hu : H.Adj (false,x) u)
    (hv : H.Adj (false,x) v)
    (huv : H.Adj u v) :
    u.2 ≠ x ∧ v.2 ≠ x := by
  have hOne (a b : Bool × V)
      (ha : H.Adj (false,x) a)
      (hb : H.Adj (false,x) b)
      (hab : H.Adj a b) : a.2 ≠ x := by
    rcases a with ⟨layer,y⟩
    change y ≠ x
    intro h
    subst y
    cases layer with
    | false =>
        exact H.irrefl ha
    | true =>
        exact taylor_mates_no_common_neighbour
          G H he hr x b ⟨hb,hab⟩
  exact ⟨hOne u v hu hv huv, hOne v u hv hu huv.symm⟩

/-- The two other vertices of any Taylor triangle through
(false,x) have different base coordinates. In particular, no
optional mate edge can be used as one side of the triangle. -/
theorem taylor_triangle_other_fibres_distinct {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x : V) (u v : Bool × V)
    (hu : H.Adj (false,x) u)
    (hv : H.Adj (false,x) v)
    (huv : H.Adj u v) :
    u.2 ≠ v.2 := by
  rcases u with ⟨a,y⟩
  rcases v with ⟨b,z⟩
  change y ≠ z
  intro h
  subst z
  cases a with
  | false =>
      cases b with
      | false =>
          exact H.irrefl huv
      | true =>
          exact taylor_mates_no_common_neighbour
            G H he hr y (false,x) ⟨hu.symm,hv.symm⟩
  | true =>
      cases b with
      | false =>
          exact taylor_mates_no_common_neighbour
            G H he hr y (false,x) ⟨hv.symm,hu.symm⟩
      | true =>
          exact H.irrefl huv

/-- Ordered triangle pairs at (false,x) with prescribed layers
for the other two vertices. No base graph or clique decomposition
is required for this finite definition. -/
noncomputable def taylorTriangleLayerPairs {V : Type*}
    [Fintype V] (H : SimpleGraph (Bool × V))
    (x : V) (a b : Bool) : Finset (V × V) := by
  classical
  exact (Finset.univ : Finset (V × V)).filter
    (fun yz => H.Adj (false,x) (a,yz.1) ∧
      H.Adj (false,x) (b,yz.2) ∧
      H.Adj (a,yz.1) (b,yz.2))

theorem mem_taylorTriangleLayerPairs {V : Type*}
    [Fintype V] (H : SimpleGraph (Bool × V))
    (x : V) (a b : Bool) (y z : V) :
    (y,z) ∈ taylorTriangleLayerPairs H x a b ↔
      (H.Adj (false,x) (a,y) ∧
        H.Adj (false,x) (b,z) ∧ H.Adj (a,y) (b,z)) := by
  classical
  simp [taylorTriangleLayerPairs]

end EPPAIII.DoubleCover
