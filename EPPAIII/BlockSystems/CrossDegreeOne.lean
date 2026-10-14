import EPPAIII.BlockSystems.MixedPieceConnectivity
import EPPAIII.BlockSystems.ClosedConnectedComponents
import EPPAIII.BlockSystems.Case1UnoccupiedBound

/-!
# Unequal mixed cross-edge component sizes force r = 1

Assume two distinct host block labels i,j exhaust the invariant
partition. All inter-block edges are mixed between selected and
outside vertices, and every vertex has exactly r neighbours in
the other host block.

If the selected sizes k_i,k_j are positive, unequal and satisfy
k_i+k_j=m, the two invariant mixed cross-edge pieces P(i,j)
and P(j,i) have orders 2k_i and 2k_j.

If r>=2, genuine two-point EPPA makes each piece internally
connected. Both pieces are closed under cross-block adjacency,
so they are complete connected components. Vertex transitivity
of the cross-block graph forces their sizes equal, contradicting
k_i != k_j. Thus r=1.

This theorem isolates the final mathematical obstruction.
Its assumptions are direct consequences of the previously
verified unequal-clique Case-1 reduction, not conclusions of
a chosen automorphism group action on the outside half.
-/

namespace EPPAIII.BlockSystems

/-- If two occupied blocks exhaust a transitive EPPA host and
have unequal complementary selected sizes, the common positive
cross-block neighbour degree must equal one. -/
theorem unequal_two_block_cross_degree_eq_one {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y)
    (hNoOutsideCross : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v)
    (hMixed : ∀ u v : W, (crossBlockGraph H block).Adj u v →
      (u ∈ Set.range e ∧ v ∉ Set.range e) ∨
      (u ∉ Set.range e ∧ v ∈ Set.range e))
    (i j : B) (hij : i ≠ j)
    (hTwo : ∀ b : B, b = i ∨ b = j)
    (hi : i ∈ occupiedBlocks e block)
    (hj : j ∈ occupiedBlocks e block)
    (m : ℕ)
    (hSize : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun v => block v = b)).card = m)
    (hComplement :
      (selectedInBlock e block i).card +
        (selectedInBlock e block j).card = m)
    (hDifferent :
      (selectedInBlock e block i).card ≠
        (selectedInBlock e block j).card)
    (r : ℕ) (hr : 0 < r)
    (hDegree : ∀ u : W, ∀ b : B, block u ≠ b →
      neighboursInBlock H block u b = r) :
    r = 1 := by
  classical
  by_contra hrNotOne
  have hrTwo : 2 ≤ r := by omega
  have hPositiveSelected (b : B)
      (hb : b ∈ occupiedBlocks e block) :
      0 < (selectedInBlock e block b).card := by
    obtain ⟨x,hx⟩ := (mem_occupiedBlocks e block b).mp hb
    apply Finset.card_pos.mpr
    refine ⟨x,Finset.mem_filter.mpr ?_⟩
    exact ⟨Finset.mem_univ _,hx⟩
  have hPositiveI := hPositiveSelected i hi
  have hPositiveJ := hPositiveSelected j hj
  have hOutsideJcard :
      (outsideHostBlock e block j).card =
        (selectedInBlock e block i).card := by
    have hs := selected_outside_host_block_card e block j
    have hjSelected := selectedHostBlock_card e block j
    have hjSize := hSize j
    omega
  have hOutsideIcard :
      (outsideHostBlock e block i).card =
        (selectedInBlock e block j).card := by
    have hs := selected_outside_host_block_card e block i
    have hiSelected := selectedHostBlock_card e block i
    have hiSize := hSize i
    omega
  have hOutsideJ : (outsideHostBlock e block j).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hOutsideI : (outsideHostBlock e block i).Nonempty :=
    Finset.card_pos.mp (by omega)
  let J : SimpleGraph W := crossBlockGraph H block
  let P : Finset W := mixedCrossPiece e block i j
  let Q : Finset W := mixedCrossPiece e block j i
  have hPnonempty : P.Nonempty := by
    obtain ⟨x,hx⟩ := (mem_occupiedBlocks e block i).mp hi
    refine ⟨e x, ?_⟩
    exact (mem_mixedCrossPiece_iff e block i j (e x)).mpr
      (Or.inl ⟨hx,⟨x,rfl⟩⟩)
  have hQnonempty : Q.Nonempty := by
    obtain ⟨x,hx⟩ := (mem_occupiedBlocks e block j).mp hj
    refine ⟨e x, ?_⟩
    exact (mem_mixedCrossPiece_iff e block j i (e x)).mpr
      (Or.inl ⟨hx,⟨x,rfl⟩⟩)
  have hClosedP : ∀ a ∈ P, ∀ b : W, J.Adj a b → b ∈ P :=
    mixedCrossPiece_edge_closed H e block i j hTwo hMixed
  have hClosedQ : ∀ a ∈ Q, ∀ b : W, J.Adj a b → b ∈ Q :=
    mixedCrossPiece_edge_closed H e block j i
      (fun b => (hTwo b).symm) hMixed
  have hConnectedP :
      ∀ a ∈ P, ∀ b ∈ P, J.Reachable a b :=
    mixedCrossPiece_connected_of_degree_two
      G H e heppa block hBlocks hSame hNoOutsideCross
      r hrTwo hDegree i j hij hOutsideJ
  have hConnectedQ :
      ∀ a ∈ Q, ∀ b ∈ Q, J.Reachable a b :=
    mixedCrossPiece_connected_of_degree_two
      G H e heppa block hBlocks hSame hNoOutsideCross
      r hrTwo hDegree j i hij.symm hOutsideI
  have hJTrans :
      CliqueCovers.HasTransitiveGraphAutomorphisms J :=
    crossBlockGraph_transitive H block hBlocks hTrans
  have hEqualPieces : P.card = Q.card :=
    transitive_closed_connected_sets_card_eq
      J hJTrans P Q hPnonempty hQnonempty
      hClosedP hClosedQ hConnectedP hConnectedQ
  have hPsize : P.card = 2 * (selectedInBlock e block i).card :=
    mixedCrossPiece_card_twice_selected
      e block i j m (hSize j) hComplement
  have hQsize : Q.card = 2 * (selectedInBlock e block j).card :=
    mixedCrossPiece_card_twice_selected
      e block j i m (hSize i) (by omega)
  exact hDifferent (by omega)

end EPPAIII.BlockSystems
