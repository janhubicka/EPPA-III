import EPPAIII.BlockSystems.DegreeTwoSharedNeighbours
import EPPAIII.BlockSystems.MixedCrossPieces
import EPPAIII.BlockSystems.SharedNeighbourConnectivity
import EPPAIII.BlockSystems.UniformCrossBlockDegrees

/-!
# The bipartite cross-edge pieces are connected when r >= 2

The mixed cross-edge piece P(i,j) consists of the selected vertices
in block i and outside vertices in block j. The degree in another
block is uniformly r. If r >= 2 and an outside vertex z is available
in block j, the genuine two-point EPPA theorem proves that every
distinct selected pair in block i has a shared cross-neighbour.

Every outside vertex in j has a selected neighbour in i, since its
positive cross-degree cannot lead to another outside vertex (by
Claim 3.14). Thus P(i,j) is internally connected.

This proof does not use vertex-transitivity of the cross-edge graph,
the component cardinality theorem, or assume a perfect matching.
-/

namespace EPPAIII.BlockSystems

/-- Every outside vertex in block j has a selected neighbour in block i
when its cross-degree there is positive and outside-outside edges
cannot run between different blocks. -/
theorem outside_block_vertex_touches_selected {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (block : W → B) (i j : B) (hij : i ≠ j)
    (hNoOutsideCross : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v)
    (r : ℕ) (hr : 0 < r)
    (hDegree : ∀ u : W, ∀ b : B, block u ≠ b →
      neighboursInBlock H block u b = r)
    (v : W) (hv : v ∈ outsideHostBlock e block j) :
    ∃ u ∈ selectedHostBlock e block i,
      (crossBlockGraph H block).Adj v u := by
  classical
  obtain ⟨hvj,hvOutside⟩ :=
    (mem_outsideHostBlock_iff e block j v).mp hv
  have hvi : block v ≠ i := by
    rw [hvj]
    exact hij.symm
  have hPos : 0 < neighboursInBlock H block v i := by
    rw [hDegree v i hvi]
    exact hr
  unfold neighboursInBlock at hPos
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hPos
  obtain ⟨hui,hAdj⟩ := (Finset.mem_filter.mp hu).2
  have huSelected : u ∈ Set.range e := by
    by_contra huOutside
    have hSame := hNoOutsideCross v u hvOutside huOutside hAdj
    have hji : j = i := hvj.symm.trans (hSame.trans hui)
    exact hij hji.symm
  have hSel : u ∈ selectedHostBlock e block i :=
    (mem_selectedHostBlock_iff e block i u).mpr ⟨hui,huSelected⟩
  refine ⟨u,hSel,?_,?_⟩
  · exact hAdj
  · rw [hvj,hui]
    exact hij.symm

/-- All vertices of a mixed cross-edge piece are mutually reachable
if r >= 2, the outside side is nonempty, and the actual EPPA and
mixed-cross-edge assumptions hold. -/
theorem mixedCrossPiece_connected_of_degree_two {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y)
    (hNoOutsideCross : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v)
    (r : ℕ) (hr : 2 ≤ r)
    (hDegree : ∀ u : W, ∀ b : B, block u ≠ b →
      neighboursInBlock H block u b = r)
    (i j : B) (hij : i ≠ j)
    (hOutsideNonempty : (outsideHostBlock e block j).Nonempty) :
    ∀ u ∈ mixedCrossPiece e block i j,
      ∀ v ∈ mixedCrossPiece e block i j,
        (crossBlockGraph H block).Reachable u v := by
  classical
  obtain ⟨z,hz⟩ := hOutsideNonempty
  obtain ⟨hzj,hzOutside⟩ :=
    (mem_outsideHostBlock_iff e block j z).mp hz
  have hzi : block z ≠ i := by
    rw [hzj]
    exact hij.symm
  have hDeg : neighboursInBlock H block z i = r :=
    hDegree z i hzi
  let S := selectedHostBlock e block i
  let T := outsideHostBlock e block j
  have hShared : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      HasCommonNeighbour (crossBlockGraph H block) a b := by
    intro a ha b hb hab
    obtain ⟨x,hxa⟩ := ((mem_selectedHostBlock_iff e block i a).mp ha).2
    obtain ⟨y,hyb⟩ := ((mem_selectedHostBlock_iff e block i b).mp hb).2
    have hxi : block (e x) = i := by
      rw [hxa]
      exact ((mem_selectedHostBlock_iff e block i a).mp ha).1
    have hyi : block (e y) = i := by
      rw [hyb]
      exact ((mem_selectedHostBlock_iff e block i b).mp hb).1
    have hxy : x ≠ y := by
      intro hxy
      apply hab
      calc
        a = e x := hxa.symm
        _ = e y := by rw [hxy]
        _ = b := hyb
    have hCommon :=
      eppa_shared_cross_neighbour_of_degree_two
        G H e heppa block hBlocks hSame hNoOutsideCross
        i j hij z hzj hzOutside r hr hDeg x y hxi hyi hxy
    simpa only [hxa,hyb] using hCommon
  have hTouches : ∀ v ∈ T, ∃ u ∈ S,
      (crossBlockGraph H block).Adj v u := by
    intro v hv
    exact outside_block_vertex_touches_selected
      H e block i j hij hNoOutsideCross r (by omega) hDegree v hv
  have hAll :=
    shared_pairs_connected_union
      (crossBlockGraph H block) S T hShared hTouches
  simpa only [mixedCrossPiece] using hAll

end EPPAIII.BlockSystems
