import EPPAIII.DoubleCover.CompleteTaylor

/-!
# Triangle patterns in the Taylor double

These are graph-level, not merely numerical, triangle classifications.
They use the actual induced bottom copy and the verified Taylor
inter-fibre matrix. Vertices in different fibres are considered here;
triangles containing the optional mate edge are handled separately in
TaylorMateTriangles.

For a fixed bottom vertex (false,x), the three possible layer patterns
of the other vertices reduce respectively to:

* three bottom vertices: three base adjacencies;
* one bottom and one top: an edge and two base nonedges;
* two top vertices: two base nonedges and one edge.

This is the finite relation-level bridge needed before counting these
configurations for a disjoint union of complete graphs.
-/

namespace EPPAIII.DoubleCover

/-- For distinct fibres, bottom-to-top adjacency in a Taylor double
is precisely nonadjacency in the base. -/
theorem taylor_bottom_top_iff_nonedge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hr : RepresentsPairPattern G H taylor)
    (x y : V) (hxy : x ≠ y) :
    H.Adj (false,x) (true,y) ↔ ¬ G.Adj x y := by
  by_cases hAdj : G.Adj x y
  · have hNo : ¬ H.Adj (false,x) (true,y) := by
      have h := (hr.1 x y hxy hAdj).1
      simpa [taylor] using h
    exact ⟨fun h => False.elim (hNo h),
      fun h => False.elim (h hAdj)⟩
  · have hYes : H.Adj (false,x) (true,y) := by
      have h := (hr.2 x y hxy hAdj).1
      simpa [taylor] using h
    exact ⟨fun _ => hAdj, fun _ => hYes⟩

/-- For distinct fibres, top-to-top adjacency in a Taylor double
is precisely adjacency in the base. -/
theorem taylor_top_top_iff_edge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hr : RepresentsPairPattern G H taylor)
    (x y : V) (hxy : x ≠ y) :
    H.Adj (true,x) (true,y) ↔ G.Adj x y := by
  by_cases hAdj : G.Adj x y
  · have hYes : H.Adj (true,x) (true,y) := by
      have h := (hr.1 x y hxy hAdj).2.2
      simpa [taylor] using h
    exact ⟨fun _ => hAdj, fun _ => hYes⟩
  · have hNo : ¬ H.Adj (true,x) (true,y) := by
      have h := (hr.2 x y hxy hAdj).2.2
      simpa [taylor] using h
    exact ⟨fun h => False.elim (hNo h),
      fun h => False.elim (hAdj h)⟩

/-- Triangles on the bottom layer are exactly base triangles. -/
theorem taylor_triangle_bottom_bottom_iff {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (x y z : V) :
    (H.Adj (false,x) (false,y) ∧
      H.Adj (false,x) (false,z) ∧
      H.Adj (false,y) (false,z)) ↔
    (G.Adj x y ∧ G.Adj x z ∧ G.Adj y z) := by
  constructor
  · rintro ⟨hxy,hxz,hyz⟩
    exact ⟨(he x y).mpr hxy, (he x z).mpr hxz,
      (he y z).mpr hyz⟩
  · rintro ⟨hxy,hxz,hyz⟩
    exact ⟨(he x y).mp hxy, (he x z).mp hxz,
      (he y z).mp hyz⟩

/-- The mixed-layer triangles through (false,x) correspond to
a base edge xy and two base nonedges xz, yz. -/
theorem taylor_triangle_bottom_mixed_iff {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x y z : V) (hxz : x ≠ z) (hyz : y ≠ z) :
    (H.Adj (false,x) (false,y) ∧
      H.Adj (false,x) (true,z) ∧
      H.Adj (false,y) (true,z)) ↔
    (G.Adj x y ∧ ¬ G.Adj x z ∧ ¬ G.Adj y z) := by
  constructor
  · rintro ⟨hxy,hxz',hyz'⟩
    exact ⟨(he x y).mpr hxy,
      (taylor_bottom_top_iff_nonedge G H hr x z hxz).mp hxz',
      (taylor_bottom_top_iff_nonedge G H hr y z hyz).mp hyz'⟩
  · rintro ⟨hxy,hxz',hyz'⟩
    exact ⟨(he x y).mp hxy,
      (taylor_bottom_top_iff_nonedge G H hr x z hxz).mpr hxz',
      (taylor_bottom_top_iff_nonedge G H hr y z hyz).mpr hyz'⟩

/-- The top-top triangles through (false,x) correspond to
a base edge yz with neither y nor z adjacent to x. -/
theorem taylor_triangle_bottom_top_top_iff {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hr : RepresentsPairPattern G H taylor)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (H.Adj (false,x) (true,y) ∧
      H.Adj (false,x) (true,z) ∧
      H.Adj (true,y) (true,z)) ↔
    (¬ G.Adj x y ∧ ¬ G.Adj x z ∧ G.Adj y z) := by
  constructor
  · rintro ⟨hxy',hxz',hyz'⟩
    exact ⟨(taylor_bottom_top_iff_nonedge G H hr x y hxy).mp hxy',
      (taylor_bottom_top_iff_nonedge G H hr x z hxz).mp hxz',
      (taylor_top_top_iff_edge G H hr y z hyz).mp hyz'⟩
  · rintro ⟨hxy',hxz',hyz'⟩
    exact ⟨(taylor_bottom_top_iff_nonedge G H hr x y hxy).mpr hxy',
      (taylor_bottom_top_iff_nonedge G H hr x z hxz).mpr hxz',
      (taylor_top_top_iff_edge G H hr y z hyz).mpr hyz'⟩

end EPPAIII.DoubleCover
