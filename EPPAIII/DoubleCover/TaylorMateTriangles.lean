import EPPAIII.DoubleCover.CompleteTaylor

/-!
# Taylor double: mate edges cannot belong to triangles

In the canonical Taylor inter-fibre pattern, the two vertices
(false,x) and (true,x) of one fibre have no common neighbour.

For a distinct base vertex y, if x and y are adjacent, the
off-diagonal cross edges between their fibres are absent.
If x and y are nonadjacent, then both same-layer edges are
absent. In either case a third vertex cannot be adjacent to
both fibre mates. Vertices in the same fibre cannot help
because the graph is loopless.

Thus the optional uniform matching of fibre mates contributes
no triangles. This is a graph-level ingredient of the Case-2
triangle-count formula, independent of the graph's component
sizes and of any coherence of the EPPA extensions.
-/

namespace EPPAIII.DoubleCover

/-- A Taylor fibre pair has no common neighbour, regardless of
whether its optional mate edge is present. -/
theorem taylor_mates_no_common_neighbour {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x : V) (w : Bool × V) :
    ¬ (H.Adj (false,x) w ∧ H.Adj (true,x) w) := by
  rintro ⟨hFalse,hTrue⟩
  rcases w with ⟨b,y⟩
  by_cases hSame : x = y
  · subst y
    cases b with
    | false => exact H.irrefl hFalse
    | true => exact H.irrefl hTrue
  by_cases hAdj : G.Adj x y
  · cases b with
    | false =>
        have hNo : ¬ H.Adj (true,x) (false,y) := by
          have h := (hr.1 x y hSame hAdj).2.1
          simpa [taylor] using h
        exact hNo hTrue
    | true =>
        have hNo : ¬ H.Adj (false,x) (true,y) := by
          have h := (hr.1 x y hSame hAdj).1
          simpa [taylor] using h
        exact hNo hFalse
  · cases b with
    | false =>
        have hNo : ¬ H.Adj (false,x) (false,y) :=
          fun h => hAdj ((he x y).mpr h)
        exact hNo hFalse
    | true =>
        have hNo : ¬ H.Adj (true,x) (true,y) := by
          have h := (hr.2 x y hSame hAdj).2.2
          simpa [taylor] using h
        exact hNo hTrue

/-- Adding or removing a mate edge cannot add a triangle through
that edge, because the mates have no common third neighbour. -/
theorem taylor_no_triangle_containing_mate_edge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x : V) (w : Bool × V) :
    ¬ (H.Adj (false,x) (true,x) ∧
       H.Adj (false,x) w ∧ H.Adj (true,x) w) := by
  rintro ⟨_,hFW,hTW⟩
  exact taylor_mates_no_common_neighbour G H he hr x w ⟨hFW,hTW⟩

end EPPAIII.DoubleCover
