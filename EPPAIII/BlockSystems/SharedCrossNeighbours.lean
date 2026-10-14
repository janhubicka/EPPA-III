import EPPAIII.BlockSystems.Claim314CrossEdges
import EPPAIII.DoubleCover.TwoPointAction

/-!
# Two-point EPPA transports shared cross-block neighbours

The cross-block graph keeps only edges joining distinct invariant
blocks of the host H. Because it is invariant under actual H
automorphisms, an EPPA lift taking an ordered selected pair (x,y)
to another selected pair (u,v) of the same adjacency type also
transports every common cross-block neighbour of e(x),e(y)
to a common cross-block neighbour of e(u),e(v).

In particular, existence of a shared cross-block neighbour is
constant on all ordered distinct base pairs of one adjacency
type. This is the EPPA orbit lemma used in the final r>=2
connected-component contradiction of unequal-clique Case 1.
-/

namespace EPPAIII.BlockSystems

/-- The relation of having a common neighbour in a graph. -/
def HasCommonNeighbour {W : Type*}
    (J : SimpleGraph W) (u v : W) : Prop :=
  ∃ z : W, J.Adj u z ∧ J.Adj v z

/-- Actual automorphisms preserve the common-neighbour relation. -/
theorem graphAutomorphism_common_neighbour {W : Type*}
    (J : SimpleGraph W)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism J q)
    (u v : W) :
    HasCommonNeighbour J u v ↔ HasCommonNeighbour J (q u) (q v) := by
  constructor
  · rintro ⟨z,huz,hvz⟩
    exact ⟨q z,(hq u z).mp huz,(hq v z).mp hvz⟩
  · rintro ⟨z,huz,hvz⟩
    refine ⟨q.symm z, ?_, ?_⟩
    · apply (hq u (q.symm z)).mpr
      simpa using huz
    · apply (hq v (q.symm z)).mpr
      simpa using hvz

/-- Every two ordered distinct base pairs of the same
adjacency type have the same shared-neighbour relation in
the actual cross-block graph of an invariant EPPA host. -/
theorem eppa_common_cross_neighbour_pair_invariant
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hType : G.Adj x y ↔ G.Adj u v) :
    HasCommonNeighbour (crossBlockGraph H block) (e x) (e y) ↔
      HasCommonNeighbour (crossBlockGraph H block) (e u) (e v) := by
  classical
  obtain ⟨p,hpx,hpy,hPartial⟩ :=
    DoubleCover.partial_of_two_maps G x y u v hxy huv hType
  obtain ⟨q,hq,hExtend⟩ :=
    heppa.2 ({x,y} : Finset V) p hPartial
  have hqx : q (e x) = e u := by
    simpa [hpx] using hExtend x (by simp)
  have hqy : q (e y) = e v := by
    simpa [hpy] using hExtend y (by simp)
  have hAutCross : IsGraphAutomorphism
      (crossBlockGraph H block) q :=
    crossBlockGraph_graphAut H block hBlocks q hq
  simpa only [hqx,hqy] using
    graphAutomorphism_common_neighbour
      (crossBlockGraph H block) q hAutCross (e x) (e y)

end EPPAIII.BlockSystems
