import EPPAIII.DoubleCover.FibreOrbits

/-!
# The deck involution and edge/nonedge status between two fibres

For a Taylor double, over distinct fibres the adjacency is completely
determined by whether the two layer bits agree and whether their
base vertices are adjacent. This holds equally when all mate edges
are present: the mate edges occur inside the fibres and do not change
inter-fibre adjacency.

The involution simultaneously exchanging all fibre mates preserves
the host graph. For a fixed ordered pair of distinct fibres, the
two ordered pairs of each adjacency status are exchanged by this
involution; no arbitrary switching of individual fibres is assumed.
-/

namespace EPPAIII.DoubleCover

/-- Inter-fibre top-top adjacency equals bottom-bottom adjacency
under the verified Taylor matrix. -/
theorem taylor_top_adj_iff_base {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hr : RepresentsPairPattern G H taylor)
    (x y : V) (hxy : x ≠ y) :
    H.Adj (true,x) (true,y) ↔ G.Adj x y := by
  by_cases hG : G.Adj x y
  · simpa [taylor, hG] using (hr.1 x y hxy hG).2.2
  · simpa [taylor, hG] using (hr.2 x y hxy hG).2.2

/-- In a Taylor double, the two cross-layer relations on
distinct fibres agree with nonadjacency in the base graph. -/
theorem taylor_cross_adj_iff_nonedge {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hr : RepresentsPairPattern G H taylor)
    (x y : V) (hxy : x ≠ y) :
    (H.Adj (false,x) (true,y) ↔ ¬ G.Adj x y) ∧
    (H.Adj (true,x) (false,y) ↔ ¬ G.Adj x y) := by
  by_cases hG : G.Adj x y
  · constructor
    · simpa [taylor, hG] using (hr.1 x y hxy hG).1
    · simpa [taylor, hG] using (hr.1 x y hxy hG).2.1
  · constructor
    · simpa [taylor, hG] using (hr.2 x y hxy hG).1
    · simpa [taylor, hG] using (hr.2 x y hxy hG).2.1

/-- A uniform formula for all ordered pairs of distinct fibres:
an edge exists exactly when layer agreement has the same truth
value as adjacency in G. -/
theorem taylor_interfibre_adj_iff {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (b c : Bool) (x y : V) (hxy : x ≠ y) :
    H.Adj (b,x) (c,y) ↔ (b = c ↔ G.Adj x y) := by
  cases b <;> cases c
  · have hh := he x y
    change G.Adj x y ↔ H.Adj (false,x) (false,y) at hh
    simpa using hh.symm
  · simpa using (taylor_cross_adj_iff_nonedge G H hr x y hxy).1
  · simpa using (taylor_cross_adj_iff_nonedge G H hr x y hxy).2
  · simpa using taylor_top_adj_iff_base G H hr x y hxy

/-- Simultaneously interchange the two vertices in every fibre. -/
def deckSwap (V : Type*) : Equiv.Perm (Bool × V) where
  toFun := fun bx => (!bx.1, bx.2)
  invFun := fun bx => (!bx.1, bx.2)
  left_inv := by
    rintro ⟨b,x⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b,x⟩
    cases b <;> rfl

/-- The deck involution preserves any graph with the Taylor
inter-fibre pattern, regardless of mate-edge status. -/
theorem deckSwap_graph_automorphism {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor) :
    IsGraphAutomorphism H (deckSwap V) := by
  rintro ⟨b,x⟩ ⟨c,y⟩
  change H.Adj (b,x) (c,y) ↔ H.Adj (!b,x) (!c,y)
  by_cases hxy : x = y
  · subst y
    cases b <;> cases c
    · simp
    · exact H.adj_comm (false,x) (true,x)
    · exact H.adj_comm (true,x) (false,x)
    · simp
  · have h1 := taylor_interfibre_adj_iff G H he hr b c x y hxy
    have h2 := taylor_interfibre_adj_iff G H he hr (!b) (!c) x y hxy
    calc
      H.Adj (b,x) (c,y) ↔ (b = c ↔ G.Adj x y) := h1
      _ ↔ ((!b) = (!c) ↔ G.Adj x y) := by
        cases b <;> cases c <;> simp
      _ ↔ H.Adj (!b,x) (!c,y) := h2.symm

/-- At fixed ordered distinct fibres, equal adjacency status
forces two ordered vertex-pairs to be identical or to be
interchanged by the deck involution. -/
theorem taylor_pair_same_status_eq_or_deck {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (he : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hr : RepresentsPairPattern G H taylor)
    (x y : V) (hxy : x ≠ y)
    (b c b' c' : Bool)
    (hstatus : H.Adj (b,x) (c,y) ↔
      H.Adj (b',x) (c',y)) :
    (b = b' ∧ c = c') ∨ (b = !b' ∧ c = !c') := by
  have h1 := taylor_interfibre_adj_iff G H he hr b c x y hxy
  have h2 := taylor_interfibre_adj_iff G H he hr b' c' x y hxy
  have hh : (b = c ↔ G.Adj x y) ↔
      (b' = c' ↔ G.Adj x y) :=
    h1.symm.trans (hstatus.trans h2)
  cases b <;> cases c <;> cases b' <;> cases c' <;>
    simp_all

end EPPAIII.DoubleCover
