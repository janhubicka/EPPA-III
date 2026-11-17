import EPPAIII.BlockSystems.GardinerLiteralNormalization
import EPPAIII.BlockSystems.ImprimitiveClassification
import EPPAIII.EPPA.ComplementTransport
import EPPAIII.DoubleCover.HomogeneityComplement

/-!
# An arbitrary-base imprimitive EPPA classification, relative to Gardiner

This combines the source's two independent reductions:
* Proposition 6.17: G is homogeneous or a cluster graph, with an
  explicitly external finite homogeneous-graph classification;
* Lemma 5.12: G is neither cluster nor co-cluster and is nonhomogeneous,
  so the actual imprimitive host has invariant two-point fibres
  and the Taylor adjacency pattern, with optional uniform mate edges.

If G is a co-cluster rather than a cluster, complement both the
selected graph and host, preserving EPPA, transitivity, nonhomogeneity,
and the actual invariant block partition.

The conclusion is a *necessary* classification of any nonhomogeneous,
transitive, imprimitive small EPPA host, with actual fixed embeddings
and a named graph equality in each alternative. It makes no choice
of coherent EPPA extensions.

This is relative only to the published homogeneous-graph
classification. The separate homogeneous two-graph 6/10 theorem
further restricts which Taylor patterns give EPPA to some
nonhomogeneous base; that result is not assumed here.
-/

namespace EPPAIII.BlockSystems

/-- Necessary alternatives for an arbitrary selected graph G:
the classified homogeneous/cluster models, their simultaneous
complements, or a fixed-embedding Taylor double with uniformly
optional mate edges and full ordered inter-block orbit transitivity. -/
def GeneralImprimitiveHostModels
    {V W B : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (block : W → B) : Prop :=
  ImprimitiveHostModels G H e ∨
  ImprimitiveHostModels Gᶜ Hᶜ e ∨
  ((∃ φ : Bool × V ≃ W,
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
        q u = u' ∧ q v = v'))

/-- Global imprimitive necessity: no selected-base restriction is
assumed. External Gardiner is an explicit implication available for
every homogeneous graph on the *same nonempty finite vertex type*.

The graph-theoretic output is deliberately a disjunction, not an
unverified claim that all Taylor and canonical host models have
the EPPA property.
-/
theorem nonhomogeneous_transitive_imprimitive_eppa_global_classification
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hNonhomogeneousH : ¬ DoubleCover.IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hGardiner : ∀ K : SimpleGraph V,
      DoubleCover.IsHomogeneousGraph K → GardinerPublishedModels K) :
    Fintype.card W = 2 * Fintype.card V ∧
      GeneralImprimitiveHostModels G H e block := by
  classical
  have hDouble : Fintype.card W = 2 * Fintype.card V :=
    nonhomogeneous_imprimitive_eppa_host_exactly_double
      G H e heppa block hBlocks hSurj hTrans
      hNonhomogeneousH hManyBlocks hNontrivial hBound
  refine ⟨hDouble, ?_⟩
  by_cases hHom : DoubleCover.IsHomogeneousGraph G
  · have hCases :=
      imprimitive_actual_host_classification_from_published_gardiner
        G H e heppa block hBlocks hSurj hTrans hNonhomogeneousH
        hManyBlocks hNontrivial hBound (Or.inl hHom)
        (hGardiner G)
    exact Or.inl hCases.2
  by_cases hCluster : IsClusterGraph G
  · have hCases :=
      imprimitive_actual_host_classification_from_published_gardiner
        G H e heppa block hBlocks hSurj hTrans hNonhomogeneousH
        hManyBlocks hNontrivial hBound (Or.inr hCluster)
        (hGardiner G)
    exact Or.inl hCases.2
  by_cases hCoCluster : IsCoClusterGraph G
  · have hClusterC : IsClusterGraph Gᶜ := by
      intro a b c hab hbc hac
      change a ≠ b ∧ ¬ G.Adj a b at hab
      change b ≠ c ∧ ¬ G.Adj b c at hbc
      change a ≠ c ∧ ¬ G.Adj a c
      exact ⟨hac,hCoCluster a b c hab.1 hbc.1 hac hab.2 hbc.2⟩
    have hEPPAc : IsEPPAEmbedding Gᶜ Hᶜ e :=
      EPPAIII.eppa_embedding_complement G H e heppa
    have hTransc : IsVertexTransitive Hᶜ :=
      transitive_complement H hTrans
    have hBlocksc : InvariantBlockMap Hᶜ block := by
      intro q hq x y
      have hOrig : IsGraphAutomorphism H q := by
        simpa using (graphAutomorphism_complement Hᶜ q hq)
      exact hBlocks q hOrig x y
    have hNonhomogeneousC : ¬ DoubleCover.IsHomogeneousGraph Hᶜ :=
      (DoubleCover.nonhomogeneous_complement_iff H).mp
        hNonhomogeneousH
    have hCases :=
      imprimitive_actual_host_classification_from_published_gardiner
        Gᶜ Hᶜ e hEPPAc block hBlocksc hSurj hTransc
        hNonhomogeneousC hManyBlocks hNontrivial hBound
        (Or.inr hClusterC) (hGardiner Gᶜ)
    exact Or.inr (Or.inl hCases.2)
  · have hTaylor :=
      transitive_eppa_double_cover_classification
        G H e heppa block hTrans hBlocks hSurj
        hHom hCluster hCoCluster hManyBlocks hNontrivial hDouble
    exact Or.inr (Or.inr hTaylor)

end EPPAIII.BlockSystems
