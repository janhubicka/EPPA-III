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

/-- If the two inter-fibre matrix types have different edge counts,
every fibre permutation induced by an automorphism of H is already
an automorphism of the bottom graph G. -/
theorem fibre_projection_automorphism_of_unequal_counts {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (p : PairPattern)
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H p)
    (hunequal : p.edgeCount ≠ p.nonedgeCount)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hq : IsGraphAutomorphism H q)
    (hσ : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) :
    IsGraphAutomorphism G σ := by
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  have hsxy : σ x ≠ σ y := σ.injective.ne hxy
  have hinv := fibreEdgeCount_invariant H q σ hq hσ x y
  constructor
  · intro hE
    by_contra hnE
    have hleft := fibreEdgeCount_edge G H p he hr x y hE
    have hright := fibreEdgeCount_nonedge G H p he hr (σ x) (σ y) hsxy hnE
    exact hunequal (hleft.symm.trans (hinv.trans hright))
  · intro hE
    by_contra hnE
    have hleft := fibreEdgeCount_nonedge G H p he hr x y hxy hnE
    have hright := fibreEdgeCount_edge G H p he hr (σ x) (σ y) hE
    exact hunequal (hright.symm.trans (hinv.symm.trans hleft))

/-- Under genuine EPPA, unequal edge counts of the fibre-pair
matrices would force the selected base graph to be homogeneous. -/
theorem homogeneous_of_unequal_pair_counts {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (p : PairPattern) (hr : RepresentsPairPattern G H p)
    (hunequal : p.edgeCount ≠ p.nonedgeCount) :
    IsHomogeneousGraph G := by
  intro D f hpartial
  obtain ⟨q,hq,hExt⟩ := heppa.2 D f hpartial
  obtain ⟨σ,hσ⟩ := hPairs q hq
  have hAut : IsGraphAutomorphism G σ :=
    fibre_projection_automorphism_of_unequal_counts
      G H p heppa.1 hr hunequal q σ hq hσ
  refine ⟨σ,hAut,?_⟩
  intro x hx
  have hExtx := hExt x hx
  have hSecond : (q (false,x)).2 = f x :=
    congrArg Prod.snd hExtx
  exact (hσ false x).symm.trans hSecond

/-- The precise missing equality in the two-point proof of Lemma 3.3:
non-homogeneity and EPPA imply that the two fibre matrix types
have equal numbers of edges. -/
theorem balanced_of_nonhomogeneous {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (p : PairPattern) (hr : RepresentsPairPattern G H p)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    p.edgeCount = p.nonedgeCount := by
  by_contra hne
  exact hNonHomogeneous
    (homogeneous_of_unequal_pair_counts G H heppa hPairs p hr hne)

/-- Combining the actual graph-level count lemma with the exhaustive
four-Boolean arithmetic, the only possible matrix patterns for a
non-homogeneous base are the one-edge, Taylor, and three-edge cases. -/
theorem nonhomogeneous_pair_pattern_cases {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (p : PairPattern) (hr : RepresentsPairPattern G H p)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    p = oneEdge ∨ p = taylor ∨ p = threeEdges :=
  balanced_cases p
    (balanced_of_nonhomogeneous G H heppa hPairs p hr hNonHomogeneous)


end EPPAIII.DoubleCover
