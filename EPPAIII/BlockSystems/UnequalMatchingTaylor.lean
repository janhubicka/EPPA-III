import EPPAIII.BlockSystems.InvariantPerfectMatchingPairs
import EPPAIII.BlockSystems.UnequalActualHostConclusion
import EPPAIII.DoubleCover.CompleteTaylor

/-!
# Unequal-clique Case 1: matching fibres force Taylor adjacency

The cross-block perfect matching is invariant under every graph
automorphism. It pairs each selected base vertex with its unique
outside mate, without labelling the outside half in advance.
Applying the verified invariant-pair EPPA theorem then identifies
the entire host with a Taylor double, up to uniform mate edges.
-/

namespace EPPAIII.BlockSystems

theorem eppa_case1_perfect_matching_is_taylor_up_to_mate
    {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ a b : V, block (e a) ≠ block (e b))
    (hNonHom : ¬ DoubleCover.IsHomogeneousGraph G)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hPerfect : ∀ u : W, ∃! v : W,
      (crossBlockGraph H block).Adj u v) :
    ∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      ∃ mate : Bool,
        (∀ x : V, H.Adj (φ (false,x)) (φ (true,x)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern G
          (pullbackGraph H φ) DoubleCover.taylor := by
  classical
  let J : SimpleGraph W := crossBlockGraph H block
  have hSelected : ∀ x y : V, ¬ J.Adj (e x) (e y) := by
    intro x y h
    have hG : G.Adj x y := (heppa.1 x y).mpr h.1
    have hSame : block (e x) = block (e y) :=
      (eppa_base_same_block_iff_eq_or_adj
        G H e heppa block hBlocks hOneEdge hNotWhole x y).mpr
        (Or.inr hG)
    exact h.2 hSame
  have hInvariant : ∀ q : Equiv.Perm W,
      IsGraphAutomorphism H q → IsGraphAutomorphism J q := by
    intro q hq
    exact crossBlockGraph_graphAut H block hBlocks q hq
  obtain ⟨φ,hBase,hPairs⟩ :=
    invariant_perfect_matching_yields_pairs
      H J e hDouble hPerfect hSelected hInvariant
  have hEPPA : IsEPPAEmbedding G (pullbackGraph H φ)
      (DoubleCover.bottomEmbedding V) :=
    eppa_pullback_bottom G H e heppa φ hBase
  obtain ⟨mate,hMate,hTaylor⟩ :=
    DoubleCover.eppa_taylor_double_up_to_mate
      G (pullbackGraph H φ) hEPPA hPairs hNonHom
  exact ⟨φ,hBase,mate,hMate,hTaylor⟩

end EPPAIII.BlockSystems
