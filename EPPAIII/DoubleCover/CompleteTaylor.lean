import EPPAIII.DoubleCover.OptionalMate

/-!
# Removing unnecessary edge/nonedge witnesses

Non-homogeneity already guarantees that the finite base graph has an edge
and a distinct nonedge. The previous exact EPPA/Taylor theorem required
explicit examples only to instantiate the four Boolean parameters.

This module supplies those examples constructively in Lean (with classical
finite logic) and states the resulting conditional double-cover theorem
without artificial parameters.
-/

namespace EPPAIII.DoubleCover

/-- Every edgeless graph is homogeneous: every permutation of its vertices
is an automorphism and extends every partial automorphism. -/
theorem homogeneous_of_edgeless {V : Type*}
    (G : SimpleGraph V)
    (hEmpty : ∀ x y : V, ¬ G.Adj x y) :
    IsHomogeneousGraph G := by
  intro D p _
  refine ⟨p, ?_, ?_⟩
  · intro x y
    exact ⟨fun h => False.elim (hEmpty x y h),
      fun h => False.elim (hEmpty (p x) (p y) h)⟩
  · intro x _
    rfl

/-- Every complete graph (all distinct points are adjacent) is
homogeneous, independently of finiteness. -/
theorem homogeneous_of_complete {V : Type*}
    (G : SimpleGraph V)
    (hComplete : ∀ x y : V, x ≠ y → G.Adj x y) :
    IsHomogeneousGraph G := by
  classical
  intro D p _
  refine ⟨p, ?_, ?_⟩
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp
    · have hne : p x ≠ p y := p.injective.ne hxy
      exact ⟨fun _ => hComplete (p x) (p y) hne,
        fun _ => hComplete x y hxy⟩
  · intro x _
    rfl

/-- A non-homogeneous graph necessarily contains an edge and a
distinct nonedge. No size parameter or arbitrary choice of
representative vertices needs to occur in the final theorem. -/
theorem edge_and_nonedge_of_nonhomogeneous {V : Type*}
    (G : SimpleGraph V)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ xe ye xn yn : V,
      G.Adj xe ye ∧ xn ≠ yn ∧ ¬ G.Adj xn yn := by
  classical
  have hEdge : ∃ xe ye : V, G.Adj xe ye := by
    by_contra hNo
    push_neg at hNo
    exact hNonHomogeneous (homogeneous_of_edgeless G hNo)
  have hNonedge : ∃ xn yn : V, xn ≠ yn ∧ ¬ G.Adj xn yn := by
    by_contra hNo
    push_neg at hNo
    exact hNonHomogeneous (homogeneous_of_complete G hNo)
  obtain ⟨xe, ye, hE⟩ := hEdge
  obtain ⟨xn, yn, hN, hnE⟩ := hNonedge
  exact ⟨xe, ye, xn, yn, hE, hN, hnE⟩

/-- Final Lean-verified two-point conclusion, conditional only on the
invariant pair system: the induced copy of any non-homogeneous G in
a two-point-fibre EPPA witness is the Taylor double between fibres,
and its mate edges are uniformly all present or all absent. -/
theorem eppa_taylor_double_up_to_mate {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ mate : Bool,
      (∀ x : V, H.Adj (false,x) (true,x) ↔ mate = true) ∧
      RepresentsPairPattern G H taylor := by
  obtain ⟨xe, ye, xn, yn, hEdge, hDistinct, hNonedge⟩ :=
    edge_and_nonedge_of_nonhomogeneous G hNonHomogeneous
  exact eppa_taylor_with_optional_mate G H heppa hPairs
    hNonHomogeneous xe ye xn yn hEdge hDistinct hNonedge

end EPPAIII.DoubleCover
