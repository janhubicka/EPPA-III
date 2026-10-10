import EPPAIII.DoubleCover.UniformPattern

/-!
# Inter-fibre edge counts

An automorphism preserving the two-element fibre partition maps a pair
of fibres to another pair. It therefore preserves the *number* of edges
between the fibres, even if it flips the two fibres independently.

The next lemmas connect this invariant to the four Boolean parameters
proved to exist in UniformPattern. This is the key missing numerical
bridge in Lemma 3.3 of EPPA--III.

No new axioms or assumptions about a coherent group action are added.
-/

namespace EPPAIII.DoubleCover

/-- The number of edges between two distinct two-element fibres,
counted once using the first fibre as the left endpoint. -/
noncomputable def fibreEdgeCount {V : Type*}
    (H : SimpleGraph (Bool × V)) (x y : V) : Nat := by
  classical
  exact
    (if H.Adj (false,x) (false,y) then 1 else 0) +
    (if H.Adj (false,x) (true,y) then 1 else 0) +
    (if H.Adj (true,x) (false,y) then 1 else 0) +
    (if H.Adj (true,x) (true,y) then 1 else 0)

/-- Invariance of the four inter-fibre edges under a graph
automorphism that preserves the system of two-element fibres. -/
theorem fibreEdgeCount_invariant {V : Type*}
    (H : SimpleGraph (Bool × V))
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hq : IsGraphAutomorphism H q)
    (hσ : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (x y : V) :
    fibreEdgeCount H x y = fibreEdgeCount H (σ x) (σ y) := by
  classical
  have hfx : q (false,x) = ((q (false,x)).1, σ x) :=
    Prod.ext rfl (hσ false x)
  have hfy : q (false,y) = ((q (false,y)).1, σ y) :=
    Prod.ext rfl (hσ false y)
  have htx : q (true,x) = (!(q (false,x)).1, σ x) :=
    Prod.ext (fibre_layer_complement q σ hσ x) (hσ true x)
  have hty : q (true,y) = (!(q (false,y)).1, σ y) :=
    Prod.ext (fibre_layer_complement q σ hσ y) (hσ true y)
  unfold fibreEdgeCount
  rw [hq (false,x) (false,y), hq (false,x) (true,y),
      hq (true,x) (false,y), hq (true,x) (true,y)]
  rw [hfx, hfy, htx, hty]
  cases hx : (q (false,x)).1 <;> cases hy : (q (false,y)).1 <;>
    simp [hx, hy, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem if_one_of_bool {P : Prop} [Decidable P]
    (b : Bool) (h : P ↔ b = true) :
    (if P then (1 : Nat) else 0) = (if b then 1 else 0) := by
  cases b <;> simp_all

/-- Over a base edge, the actual inter-fibre edge count equals
the prescribed numerical count of the edge-type matrix. -/
theorem fibreEdgeCount_edge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (p : PairPattern) (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H p)
    (x y : V) (hxy : G.Adj x y) :
    fibreEdgeCount H x y = p.edgeCount := by
  classical
  have hbottom : H.Adj (false,x) (false,y) := (he x y).mp hxy
  have hne : x ≠ y := G.ne_of_adj hxy
  obtain ⟨hc1,hc2,ht⟩ := hr.1 x y hne hxy
  simp only [fibreEdgeCount, if_pos hbottom]
  rw [if_one_of_bool p.crossEdge hc1,
      if_one_of_bool p.crossEdge hc2,
      if_one_of_bool p.topEdge ht]
  cases hc : p.crossEdge <;> cases ht' : p.topEdge <;>
    simp [PairPattern.edgeCount, hc, ht', Nat.add_assoc]

/-- Over a base nonedge, the actual inter-fibre edge count equals
the prescribed numerical count of the nonedge-type matrix. -/
theorem fibreEdgeCount_nonedge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (p : PairPattern) (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H p)
    (x y : V) (hxy : x ≠ y) (hnot : ¬ G.Adj x y) :
    fibreEdgeCount H x y = p.nonedgeCount := by
  classical
  have hbottom : ¬ H.Adj (false,x) (false,y) :=
    fun h => hnot ((he x y).mpr h)
  obtain ⟨hc1,hc2,ht⟩ := hr.2 x y hxy hnot
  simp only [fibreEdgeCount, if_neg hbottom]
  rw [if_one_of_bool p.crossNonedge hc1,
      if_one_of_bool p.crossNonedge hc2,
      if_one_of_bool p.topNonedge ht]
  cases hc : p.crossNonedge <;> cases ht' : p.topNonedge <;>
    simp [PairPattern.nonedgeCount, hc, ht', Nat.add_assoc]

end EPPAIII.DoubleCover
