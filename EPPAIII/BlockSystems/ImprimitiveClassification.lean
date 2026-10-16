import EPPAIII.BlockSystems.OrderedInterblockOrbits

/-!
# Imprimitive double-cover classification (current Lemma 5.12)

The source is main-new(8).tex, Section 5.3 (lemma:doublecover).
Formerly this was Lemma 3.3 in the unmerged manuscript.

Combines the verified pair-system reduction, the Taylor inter-fibre
adjacency pattern with optional uniform mate edges, and the orbit
transitivity of ordered inter-block edges and nonedges. Coordinates
of the second half are constructed, not postulated. No coherent EPPA
lifts are required.

Non-homogeneity of G is explicit; deriving it from the excluded
Gardiner classes is a separate manuscript-level dependency.
-/

namespace EPPAIII.BlockSystems

/-- Full actual-host double-cover conclusion under a non-homogeneous
base, with inter-block orbit transitivity in the original host. -/
theorem transitive_eppa_double_cover_classification
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
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
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    (∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      ∃ mate : Bool,
        (∀ x : V, H.Adj (φ (false,x)) (φ (true,x)) ↔
          mate = true) ∧
        DoubleCover.RepresentsPairPattern
          G (pullbackGraph H φ) DoubleCover.taylor) ∧
    (∀ u v u' v' : W,
      block u ≠ block v →
      block u' ≠ block v' →
      (H.Adj u v ↔ H.Adj u' v') →
      ∃ q : Equiv.Perm W,
        IsGraphAutomorphism H q ∧
        q u = u' ∧ q v = v') := by
  constructor
  · exact transitive_eppa_double_cover_up_to_mate
      G H e heppa block hTrans hBlocks hSurj
      hNonHomogeneous hNonCluster hNonCoCluster
      hManyBlocks hNontrivial hHostSize
  · intro u v u' v' hDifferent hDifferent' hStatus
    exact transitive_eppa_host_interblock_status_orbit
      G H e heppa block hTrans hBlocks hSurj
      hNonHomogeneous hNonCluster hNonCoCluster
      hManyBlocks hNontrivial hHostSize
      u v u' v' hDifferent hDifferent' hStatus

end EPPAIII.BlockSystems
