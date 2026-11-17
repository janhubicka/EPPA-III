import EPPAIII.BlockSystems.ImprimitiveProposition617
import EPPAIII.BlockSystems.ClusterRegularHomogeneity

/-!
# Final source-facing Proposition 6.17 relative only to Gardiner

For an arbitrary finite base G assumed homogeneous or a union of
cliques, the elementary cluster-degree dichotomy reduces the
nonhomogeneous clique union to the unequal-component case. If G is
homogeneous, apply Gardiner's external classification, supplied as
a normal-form hypothesis with explicit base graph equivalences.

No extra host hypotheses or extra graph classifications are assumed.
The imported Gardiner statement is NOT asserted as a new Lean axiom.
-/

namespace EPPAIII.BlockSystems

/-- The four canonical model types of Gardiner's classification,
using self-complementarity of C5 and the 3x3 rook graph to normalize
those models. This is an external theorem input, not a theorem
claimed here. -/
def GardinerHomogeneousModels {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t) G φ) ∨
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t)ᶜ G φ) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G φ) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G φ)

/-- Embed Gardiner's homogeneous cases into the five possible
selected-base types of the actual-host classification. -/
theorem gardiner_models_are_imprimitive_base_models
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (h : GardinerHomogeneousModels G) :
    ImprimitiveBaseModels G := by
  rcases h with hEq | hRest
  · exact Or.inl hEq
  rcases hRest with hCo | hRest
  · exact Or.inr (Or.inl hCo)
  rcases hRest with hCycle | hRook
  · exact Or.inr (Or.inr (Or.inl hCycle))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hRook)))

/-- The printed assumption on G suffices for the canonical
base split, using Gardiner only for homogeneous graphs. -/
theorem imprimitive_base_models_from_gardiner
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hSource : DoubleCover.IsHomogeneousGraph G ∨ IsClusterGraph G)
    (hGardiner : DoubleCover.IsHomogeneousGraph G →
      GardinerHomogeneousModels G) :
    ImprimitiveBaseModels G := by
  rcases hSource with hHom | hCluster
  · exact gardiner_models_are_imprimitive_base_models G (hGardiner hHom)
  · rcases cluster_homogeneous_or_unequal_degrees G hCluster with
      hHom | ⟨x,y,hDiff⟩
    · exact gardiner_models_are_imprimitive_base_models G (hGardiner hHom)
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hCluster,x,y,hDiff⟩)))

/-- Exact source-facing imprimitive necessity statement. The only
external input is Gardiner's finite homogeneous-graph classification
in canonical model form. -/
theorem imprimitive_actual_host_classification_from_gardiner
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ DoubleCover.IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hSource : DoubleCover.IsHomogeneousGraph G ∨ IsClusterGraph G)
    (hGardiner : DoubleCover.IsHomogeneousGraph G →
      GardinerHomogeneousModels G) :
    Fintype.card W = 2 * Fintype.card V ∧
      ImprimitiveHostModels G H e :=
  imprimitive_actual_host_classification_of_base_models
    G H e heppa block hBlocks hSurj hTrans hNonhomogeneous
    hManyBlocks hNontrivial hBound
    (imprimitive_base_models_from_gardiner G hSource hGardiner)

end EPPAIII.BlockSystems
