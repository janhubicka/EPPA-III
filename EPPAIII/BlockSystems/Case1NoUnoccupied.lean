import EPPAIII.BlockSystems.IndependentTransversalLifts
import EPPAIII.BlockSystems.UnoccupiedTouchSupport
import EPPAIII.BlockSystems.Case1UnoccupiedBound

/-!
# Excluding the final unoccupied block in unequal-clique Case 1

The full-transversal EPPA theorem supplies an automorphism fixing
a unique unoccupied block U between selected vertices belonging
to different occupied blocks. If two selected vertices are in the
same block, compose two such genuine automorphisms through a
selected vertex in a different occupied block.

This gives fixed-U transitivity on *all* selected vertices, without
choosing a coherent lifting of Aut(G). The neighbourhood-support
obstruction then excludes U whenever selected block occupancies
are unequal. Combined with the complete quotient and at-most-one-
unoccupied results, all host blocks must meet G.

This closes the "no unoccupied blocks" reduction in the Case-1
repair of Claim 3.15. The cross-degree identity and matching
classification remain separate.
-/

namespace EPPAIII.BlockSystems

/-- Fixed-U lifts between different selected blocks compose to
give fixed-U transitivity on the entire distinguished base copy,
provided at least two occupied block labels are distinct. -/
theorem eppa_fixedU_transitive_on_selected {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y)
    (U : B) (hU : U ∉ occupiedBlocks e block)
    (hOnly : ∀ b : B, b ∉ occupiedBlocks e block → b = U)
    (b c : B) (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block) (hbc : b ≠ c) :
    ∀ x y : V,
      ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q),
        q (e x) = e y ∧
        (∀ z : W, block z = U ↔ block (q z) = U) := by
  classical
  obtain ⟨rb,hrb⟩ := (mem_occupiedBlocks e block b).mp hb
  obtain ⟨rc,hrc⟩ := (mem_occupiedBlocks e block c).mp hc
  have hOther (x : V) :
      ∃ z : V, block (e x) ≠ block (e z) := by
    by_cases hxb : block (e x) = b
    · refine ⟨rc, ?_⟩
      rw [hrc]
      intro hxc
      exact hbc (hxb.symm.trans hxc)
    · refine ⟨rb, ?_⟩
      rw [hrb]
      exact hxb
  intro x y
  by_cases hDiff : block (e x) ≠ block (e y)
  · exact eppa_fixed_unoccupied_lift_between_blocks
      G H e heppa block hBlocks hSurj hSame U hU hOnly x y hDiff
  · have hSameBlock : block (e x) = block (e y) := by
      by_contra h
      exact hDiff h
    obtain ⟨z,hxz⟩ := hOther x
    have hzy : block (e z) ≠ block (e y) := by
      intro h
      exact hxz (hSameBlock.trans h.symm)
    obtain ⟨q₁,hq₁,hMap₁,hFix₁⟩ :=
      eppa_fixed_unoccupied_lift_between_blocks
        G H e heppa block hBlocks hSurj hSame U hU hOnly x z hxz
    obtain ⟨q₂,hq₂,hMap₂,hFix₂⟩ :=
      eppa_fixed_unoccupied_lift_between_blocks
        G H e heppa block hBlocks hSurj hSame U hU hOnly z y hzy
    let q : Equiv.Perm W := q₁.trans q₂
    have hq : IsGraphAutomorphism H q := by
      intro u v
      exact (hq₁ u v).trans (hq₂ (q₁ u) (q₁ v))
    have hMap : q (e x) = e y := by
      change q₂ (q₁ (e x)) = e y
      rw [hMap₁,hMap₂]
    have hFix (w : W) :
        block w = U ↔ block (q w) = U := by
      change block w = U ↔ block (q₂ (q₁ w)) = U
      exact (hFix₁ w).trans (hFix₂ (q₁ w))
    exact ⟨q,hq,hMap,hFix⟩

/-- Main Case-1 conclusion: all host blocks are occupied by G.
The proof derives block cliques, quotient completeness, and the
at-most-one-unoccupied bound before excluding the final possibility. -/
theorem eppa_case1_all_host_blocks_occupied {V W B : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hOneEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hNotWhole : ∃ x y : V, block (e x) ≠ block (e y))
    (hNonCluster : ¬ IsClusterGraph H)
    (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (b c : B)
    (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    occupiedBlocks e block = Finset.univ := by
  classical
  obtain ⟨_,hComplete,hAtMostOne⟩ :=
    eppa_case1_quotient_and_unoccupied_bound
      G H e heppa block hBlocks hSurj hTrans
      hOneEdge hNotWhole hNonCluster m hUniform hDouble
      b c hb hc hDifferent
  have hSame : ∀ x y : V,
      block (e x) = block (e y) ↔ x = y ∨ G.Adj x y :=
    eppa_base_same_block_iff_eq_or_adj
      G H e heppa block hBlocks hOneEdge hNotWhole
  have hInternal : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y) :=
    eppa_base_edges_internal_of_one G H e heppa
      block hBlocks hOneEdge
  have hNoOutsideCross : ∀ u v : W,
      u ∉ Set.range e → v ∉ Set.range e →
      H.Adj u v → block u = block v := by
    intro u v hu hv hadj
    exact no_outside_cross_block_edges
      G H e heppa.1 block hBlocks hTrans hInternal hDouble
      u v hu hv hadj
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hDifferent rfl
  by_contra hNotAll
  have hMissing : ∃ U : B, U ∉ occupiedBlocks e block := by
    by_contra hNone
    apply hNotAll
    ext i
    simp only [Finset.mem_univ, iff_true]
    by_contra hi
    exact hNone ⟨i,hi⟩
  obtain ⟨U,hU⟩ := hMissing
  have hOnly : ∀ j : B, j ∉ occupiedBlocks e block → j = U := by
    intro j hj
    by_contra hju
    have hTwo : 1 < ((occupiedBlocks e block)ᶜ).card :=
      Finset.one_lt_card.mpr
        ⟨j,by simpa using hj,U,by simpa using hU,hju⟩
    omega
  have hLifts := eppa_fixedU_transitive_on_selected
    G H e heppa block hBlocks hSurj hSame U hU hOnly
    b c hb hc hbc
  exact no_unoccupied_block_of_fixedU_selected_transitivity
    H e block U hU hComplete hNoOutsideCross hBlocks hLifts
    b c hb hc hDifferent

end EPPAIII.BlockSystems
