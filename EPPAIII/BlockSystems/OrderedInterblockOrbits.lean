import EPPAIII.DoubleCover.InterblockOrbits

/-!
# Ordered inter-block edge and nonedge transitivity in the original host

The earlier theorems established:
* the invariant two-point blocks and canonical equivalence,
* transport of EPPA and of block invariance to Bool × V,
* the Taylor inter-fibre structure and its deck involution,
* transitivity on ordered inter-fibre edges and nonedges
  in the canonical two-layer presentation.

This module transports the last orbit statement back to the *actual*
finite vertex type W of the original host. It contains the full
additional orbit conclusion of Lemma 3.3, with the same explicit
non-homogeneity and non-cluster hypotheses as the previously verified
structural theorem.
-/

namespace EPPAIII.BlockSystems

/-- Actual host automorphisms transported back along the canonical
vertex equivalence. -/
theorem pullback_automorphism_to_host {X W : Type*}
    (H : SimpleGraph W) (φ : X ≃ W)
    (q : Equiv.Perm X)
    (hq : IsGraphAutomorphism (pullbackGraph H φ) q) :
    IsGraphAutomorphism H ((φ.symm.trans q).trans φ) := by
  intro u v
  have hh := hq (φ.symm u) (φ.symm v)
  change H.Adj (φ (φ.symm u)) (φ (φ.symm v)) ↔
    H.Adj (φ (q (φ.symm u))) (φ (q (φ.symm v))) at hh
  simpa using hh

/-- Complete ordered inter-block orbit conclusion, stated entirely
on the original host rather than a chosen Bool × V presentation.

Any two ordered vertex pairs whose endpoints lie in different
imprimitivity blocks, and whose adjacency statuses agree, are
related by a genuine automorphism of H. In particular the ordered
inter-block edges form one orbit and the ordered inter-block nonedges
form one orbit. -/
theorem transitive_eppa_host_interblock_status_orbit {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (u v u' v' : W)
    (hDifferent : block u ≠ block v)
    (hDifferent' : block u' ≠ block v')
    (hStatus : H.Adj u v ↔ H.Adj u' v') :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧ q u = u' ∧ q v = v' := by
  classical
  obtain ⟨hInject, _hCount, hTwo⟩ :=
    transitive_eppa_blocks_are_pairs G H e heppa block
      hTrans hBlocks hSurj hNonHomogeneous
      hNonCluster hNonCoCluster hManyBlocks
      hNontrivial hHostSize
  obtain ⟨φ, hBottom, hPairBlock⟩ :=
    exists_canonical_pair_equiv e block hInject hTwo hHostSize
  have heppa' : IsEPPAEmbedding G (pullbackGraph H φ)
      (DoubleCover.bottomEmbedding V) :=
    eppa_pullback_bottom G H e heppa φ hBottom
  have hPairs' : DoubleCover.HasInvariantPairs (pullbackGraph H φ) :=
    invariant_pairs_of_pullback H e block hBlocks
      hInject φ hPairBlock
  have hBlockOf (w : W) :
      block w = block (e ((φ.symm w).2)) := by
    simpa using hPairBlock (φ.symm w).1 (φ.symm w).2
  have hDiffOf (w z : W) (hwz : block w ≠ block z) :
      (φ.symm w).2 ≠ (φ.symm z).2 := by
    intro hEq
    apply hwz
    calc
      block w = block (e ((φ.symm w).2)) := hBlockOf w
      _ = block (e ((φ.symm z).2)) := by rw [hEq]
      _ = block z := (hBlockOf z).symm
  have hStatus' :
      (pullbackGraph H φ).Adj (φ.symm u) (φ.symm v) ↔
      (pullbackGraph H φ).Adj (φ.symm u') (φ.symm v') := by
    change H.Adj (φ (φ.symm u)) (φ (φ.symm v)) ↔
      H.Adj (φ (φ.symm u')) (φ (φ.symm v'))
    simpa using hStatus
  have hStatus'' :
      (pullbackGraph H φ).Adj
        ((φ.symm u).1, (φ.symm u).2)
        ((φ.symm v).1, (φ.symm v).2) ↔
      (pullbackGraph H φ).Adj
        ((φ.symm u').1, (φ.symm u').2)
        ((φ.symm v').1, (φ.symm v').2) := by
    simpa using hStatus'
  obtain ⟨q',hq',hqu,hqv⟩ :=
    DoubleCover.eppa_interfibre_pair_status_transitive
      G (pullbackGraph H φ) heppa' hPairs' hNonHomogeneous
      (φ.symm u).1 (φ.symm v).1
      (φ.symm u').1 (φ.symm v').1
      (φ.symm u).2 (φ.symm v).2
      (φ.symm u').2 (φ.symm v').2
      (hDiffOf u v hDifferent)
      (hDiffOf u' v' hDifferent')
      hStatus''
  have hqu' : q' (φ.symm u) = φ.symm u' := by
    simpa using hqu
  have hqv' : q' (φ.symm v) = φ.symm v' := by
    simpa using hqv
  let qW : Equiv.Perm W := (φ.symm.trans q').trans φ
  refine ⟨qW, pullback_automorphism_to_host H φ q' hq', ?_, ?_⟩
  · change φ (q' (φ.symm u)) = u'
    rw [hqu']
    simp
  · change φ (q' (φ.symm v)) = v'
    rw [hqv']
    simp

/-- The ordered inter-block edge orbit in the actual finite host. -/
theorem transitive_eppa_host_interblock_edges {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (u v u' v' : W)
    (hDifferent : block u ≠ block v)
    (hDifferent' : block u' ≠ block v')
    (hEdge : H.Adj u v) (hEdge' : H.Adj u' v') :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧ q u = u' ∧ q v = v' := by
  exact transitive_eppa_host_interblock_status_orbit
    G H e heppa block hTrans hBlocks hSurj
    hNonHomogeneous hNonCluster hNonCoCluster
    hManyBlocks hNontrivial hHostSize
    u v u' v' hDifferent hDifferent'
    ⟨fun _ => hEdge', fun _ => hEdge⟩

/-- The ordered inter-block nonedge orbit in the actual finite host. -/
theorem transitive_eppa_host_interblock_nonedges {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (u v u' v' : W)
    (hDifferent : block u ≠ block v)
    (hDifferent' : block u' ≠ block v')
    (hNonedge : ¬ H.Adj u v) (hNonedge' : ¬ H.Adj u' v') :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧ q u = u' ∧ q v = v' := by
  exact transitive_eppa_host_interblock_status_orbit
    G H e heppa block hTrans hBlocks hSurj
    hNonHomogeneous hNonCluster hNonCoCluster
    hManyBlocks hNontrivial hHostSize
    u v u' v' hDifferent hDifferent'
    ⟨fun h => False.elim (hNonedge h),
     fun h => False.elim (hNonedge' h)⟩

end EPPAIII.BlockSystems
