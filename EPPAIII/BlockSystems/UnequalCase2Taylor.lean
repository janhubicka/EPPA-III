import EPPAIII.BlockSystems.TransitivePartition
import EPPAIII.BlockSystems.CanonicalPairs
import EPPAIII.BlockSystems.GraphTransport
import EPPAIII.DoubleCover.CompleteTaylor

/-!
# The crossing-edge Case 2 of unequal-clique Lemma 3.12

When an edge of the selected base crosses an invariant block
partition, every selected edge crosses blocks by two-point EPPA.
If G also contains an induced complement of P3, all distinct
selected nonedges likewise cross blocks. Hence the selected
copy is a transversal of the invariant block system.

For a transitive host of twice the order of G, the nontrivial
uniform block size is necessarily two, and there is exactly
one block per selected vertex. Existing canonical-pair transport
then turns the host into Bool × V with its genuine EPPA action.

For non-homogeneous G, the already verified invariant-pair
Taylor theorem identifies all inter-fibre edges as the Taylor
double, up to an optional uniform matching of mates. This
avoids replaying Claims 3.5--3.6 in the unequal-clique proof.

The remaining exclusion of more than two unequal clique
components via triangle counts is a separate obligation.
-/

namespace EPPAIII.BlockSystems

/-- Case 2 of Lemma 3.12: one crossing selected edge, together
with an induced co-P3 in the selected graph, forces every
selected vertex into a different host imprimitivity block. -/
theorem eppa_base_transversal_of_crossing_edge {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ x y : V,
      G.Adj x y ∧ block (e x) ≠ block (e y)) :
    Function.Injective (fun x : V => block (e x)) := by
  obtain ⟨u,v,huv,hCrossUV⟩ := hCross
  have hNotWhole : ∃ x y : V,
      block (e x) ≠ block (e y) := ⟨u,v,hCrossUV⟩
  have hEdgesCross : ∀ x y : V, G.Adj x y →
      block (e x) ≠ block (e y) := by
    intro x y hAdj hSame
    have hTrans := (eppa_edges_uniform_blocks
      G H e heppa block hBlocks x y u v hAdj huv).mp hSame
    exact hCrossUV hTrans
  have hNonedgesCross : ∀ x y : V, x ≠ y →
      ¬ G.Adj x y → block (e x) ≠ block (e y) :=
    nonedges_cross_of_induced_cop3
      G H e heppa block hBlocks hCoP3 hNotWhole
  intro x y hSame
  by_contra hxy
  by_cases hAdj : G.Adj x y
  · exact (hEdgesCross x y hAdj) hSame
  · exact (hNonedgesCross x y hxy hAdj) hSame

/-- Uniformity of the actual invariant blocks and the exact
double-size equation force the Case-2 fibres to be pairs.
Neither uniformity nor the block-count formula is postulated. -/
theorem transitive_eppa_crossing_edge_blocks_are_pairs {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ x y : V,
      G.Adj x y ∧ block (e x) ≠ block (e y))
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    Function.Injective (fun x : V => block (e x)) ∧
      Fintype.card B = Fintype.card V ∧
      (∀ b : B, ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 2) := by
  classical
  obtain ⟨b₀,hLarge⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal H block hTrans hBlocks hSurj b b₀
  have hOrder : Fintype.card B * m = 2 * Fintype.card V :=
    (uniform_partition_card_formula block m hUniform).trans hHostSize
  have hInject : Function.Injective (fun x : V => block (e x)) :=
    eppa_base_transversal_of_crossing_edge
      G H e heppa block hBlocks hCoP3 hCross
  have hNumber : Fintype.card V ≤ Fintype.card B :=
    Fintype.card_le_of_injective
      (fun x : V => block (e x)) hInject
  obtain ⟨hCount,hTwo⟩ :=
    transversal_double_count
      (Fintype.card B) m (Fintype.card V)
      (by omega) hLarge hNumber hOrder
  refine ⟨hInject,hCount,?_⟩
  intro b
  rw [hUniform b]
  exact hTwo

/-- Full structural Case-2 conclusion for a non-homogeneous
base with an induced co-P3: the host has the Taylor
inter-fibre matrix, with the uniform optional mate matching.
The canonical pairing is derived from the actual invariant
partition, not assumed. -/
theorem transitive_eppa_crossing_edge_taylor_up_to_mate {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ x y : V,
      G.Adj x y ∧ block (e x) ≠ block (e y))
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    ∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      ∃ mate : Bool,
        (∀ x : V, H.Adj (φ (false,x)) (φ (true,x)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern
          G (pullbackGraph H φ) DoubleCover.taylor := by
  classical
  obtain ⟨hInject,_hCount,hTwo⟩ :=
    transitive_eppa_crossing_edge_blocks_are_pairs
      G H e heppa block hBlocks hSurj hTrans hCoP3
      hCross hManyBlocks hNontrivial hHostSize
  obtain ⟨φ,hBottom,hPairBlock⟩ :=
    exists_canonical_pair_equiv e block hInject hTwo hHostSize
  have heppa' : IsEPPAEmbedding G (pullbackGraph H φ)
      (DoubleCover.bottomEmbedding V) :=
    eppa_pullback_bottom G H e heppa φ hBottom
  have hPairs' : DoubleCover.HasInvariantPairs (pullbackGraph H φ) :=
    invariant_pairs_of_pullback H e block hBlocks hInject φ hPairBlock
  obtain ⟨mate,hMate,hInter⟩ :=
    DoubleCover.eppa_taylor_double_up_to_mate
      G (pullbackGraph H φ) heppa' hPairs' hNonHomogeneous
  refine ⟨φ,hBottom,mate,?_,hInter⟩
  intro x
  exact hMate x

end EPPAIII.BlockSystems
