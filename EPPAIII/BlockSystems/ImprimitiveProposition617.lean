import EPPAIII.BlockSystems.ImprimitiveStrictOrder
import EPPAIII.BlockSystems.Section6NonhomogeneousInterfaces
import EPPAIII.CliqueCovers.Section6ComplementedCliques
import EPPAIII.BlockSystems.CycleFiveFinalImprimitiveClassification
import EPPAIII.BlockSystems.RookThreeFinalImprimitiveClassification
import EPPAIII.EPPA.BaseRelabel

/-!
# Proposition 6.17: actual-host imprimitive classification, assembled in Lean

This theorem finishes the *relative-to-Gardiner* necessity argument.
The only externally classified input is the form of the selected
homogeneous/cluster graph. It is an explicit hypothesis
`ImprimitiveBaseModels G`, not a Lean axiom or a hidden replacement
of the conclusion.

From the manuscript's actual finite EPPA embedding, transitivity,
nontrivial invariant block partition, nonhomogeneity of H, and the
upper bound |H| <= 2|G|, we prove:
* |H| = 2|G|;
* the corresponding actual-host named cover/Wagner, unequal two-clique
  matched double, C5, or 3x3 rook classification, including complements.

Every canonical-case hypothesis is transported from its model
to the actual base embedding through a bijection. None of these branches
presupposes an outside-half decomposition or coherent EPPA lift.

The existing external Gardiner classification and elementary
normalization of homogeneous cluster graphs are not proved here.
The manuscript's unrepaired English proofs are NOT certified merely
because this alternative Lean assembly compiles.
-/

namespace EPPAIII.BlockSystems

/-- A model for the selected graph, with an explicit relabelling. -/
def CanonicalBaseCopy {U V : Type*}
    (K : SimpleGraph U) (G : SimpleGraph V) (φ : U ≃ V) : Prop :=
  ∀ x y : U, K.Adj x y ↔ G.Adj (φ x) (φ y)

/-- The exact generalized-cover or Wagner output for a designated
equal-clique base embedding. This is an actual-host graph equality,
not merely an abstract graph-isomorphism type. -/
def EqualCliqueHostModels
    (s t : ℕ) {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W) : Prop :=
  (∃ (φ : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, φ (false,x) = e x) ∧
      H.comap φ = coverGraph s t X Y) ∨
  (∃ (hS : s = 2) (hT : t = 2)
      (φ : CoverVertex 2 2 ≃ W),
      (∀ x : Fin 2 × Fin 2,
        φ (false,x) =
          e (Fin.cast hS.symm x.1, Fin.cast hT.symm x.2)) ∧
      H.comap φ = CliqueCovers.wagnerCanonicalGraph)

/-- External graph-form input used for Proposition 6.17.
The first four alternatives are the canonical homogeneous
models of Gardiner (including complementary clique unions);
the final alternative is a cluster graph with unequal degrees.
This assumption explicitly isolates the unformalized external
base classification from the actual-host EPPA argument. -/
def ImprimitiveBaseModels {V : Type*} [Fintype V]
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
      CanonicalBaseCopy rookThreeGraph G φ) ∨
  (IsClusterGraph G ∧ ∃ x y : V,
    (DoubleCover.clusterBaseNeighbours G x).card ≠
      (DoubleCover.clusterBaseNeighbours G y).card)

/-- Complete concrete model list, *up to complementation*, for
the selected imprimitive EPPA host. Every alternative has a
specified fixed embedding of the canonical model of the base. -/
def ImprimitiveHostModels {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t) G φ ∧
      EqualCliqueHostModels s t H (EPPAIII.relabelEmbedding e φ)) ∨
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t)ᶜ G φ ∧
      EqualCliqueHostModels s t Hᶜ (EPPAIII.relabelEmbedding e φ)) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G φ ∧
      (CycleFiveSmallHostPatterns H (EPPAIII.relabelEmbedding e φ) ∨
       CycleFiveSmallHostPatterns Hᶜ
         (EPPAIII.relabelEmbedding
           (EPPAIII.relabelEmbedding e φ) cycleFiveDoubleIndex))) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G φ ∧
      (RookSmallHostPatterns H (EPPAIII.relabelEmbedding e φ) ∨
       RookSmallHostPatterns Hᶜ
         (EPPAIII.relabelEmbedding
           (EPPAIII.relabelEmbedding e φ) rookComplementIndex))) ∨
  (∃ (c : V → Bool) (φ : Bool × V ≃ W),
      G = twoCliqueGraph c ∧
      (∀ v : V, φ (false,v) = e v) ∧
      pullbackGraph H φ = twoCliqueMatchedGraph c true)

/-- Final imprimitive necessity under actual source hypotheses,
**relative to** the explicit selected-base model list.
No further host-structure hypotheses are assumed. -/
theorem imprimitive_actual_host_classification_of_base_models
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
    (hBase : ImprimitiveBaseModels G) :
    Fintype.card W = 2 * Fintype.card V ∧
      ImprimitiveHostModels G H e := by
  classical
  have hDouble : Fintype.card W = 2 * Fintype.card V :=
    nonhomogeneous_imprimitive_eppa_host_exactly_double
      G H e heppa block hBlocks hSurj hTrans hNonhomogeneous
      hManyBlocks hNontrivial hBound
  refine ⟨hDouble, ?_⟩
  rcases hBase with hEqual | hRest
  · obtain ⟨s,t,hs,ht,φ,hModel⟩ := hEqual
    have hEPPA :
        IsEPPAEmbedding (cliqueUnion s t) H
          (EPPAIII.relabelEmbedding e φ) :=
      EPPAIII.eppa_relabel_base G H e heppa φ
        (cliqueUnion s t) hModel
    have hCardV : Fintype.card V = s * t := by
      have hCard := Fintype.card_congr φ
      simpa only [Fintype.card_prod, Fintype.card_fin] using hCard.symm
    have hOrder : Fintype.card W = 2 * s * t := by
      calc
        Fintype.card W = 2 * Fintype.card V := hDouble
        _ = 2 * s * t := by rw [hCardV]; ring
    have hAlternative : EqualCliqueHostModels s t H
        (EPPAIII.relabelEmbedding e φ) :=
      CliqueCovers.eppa_nonhomogeneous_clique_double_all_positive
        H (EPPAIII.relabelEmbedding e φ) hEPPA hs ht hOrder
        hTrans hNonhomogeneous
    exact Or.inl ⟨s,t,hs,ht,φ,hModel,hAlternative⟩
  rcases hRest with hComplement | hRest
  · obtain ⟨s,t,hs,ht,φ,hModel⟩ := hComplement
    have hEPPA :
        IsEPPAEmbedding (cliqueUnion s t)ᶜ H
          (EPPAIII.relabelEmbedding e φ) :=
      EPPAIII.eppa_relabel_base G H e heppa φ
        (cliqueUnion s t)ᶜ hModel
    have hCardV : Fintype.card V = s * t := by
      have hCard := Fintype.card_congr φ
      simpa only [Fintype.card_prod, Fintype.card_fin] using hCard.symm
    have hOrder : Fintype.card W = 2 * s * t := by
      calc
        Fintype.card W = 2 * Fintype.card V := hDouble
        _ = 2 * s * t := by rw [hCardV]; ring
    have hAlternative : EqualCliqueHostModels s t Hᶜ
        (EPPAIII.relabelEmbedding e φ) :=
      CliqueCovers.eppa_nonhomogeneous_complement_clique_double_all_positive
        H (EPPAIII.relabelEmbedding e φ) hEPPA hs ht hOrder
        hTrans hNonhomogeneous
    exact Or.inr (Or.inl ⟨s,t,hs,ht,φ,hModel,hAlternative⟩)
  rcases hRest with hCycle | hRest
  · obtain ⟨φ,hModel⟩ := hCycle
    have hEPPA :
        IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H
          (EPPAIII.relabelEmbedding e φ) :=
      EPPAIII.eppa_relabel_base G H e heppa φ
        (SimpleGraph.cycleGraph 5) hModel
    have hCardV : Fintype.card V = 5 := by
      simpa using (Fintype.card_congr φ).symm
    have hTen : Fintype.card W = 10 := by omega
    have hCases :=
      cycleFive_eppa_imprimitive_models_up_to_complement
        H (EPPAIII.relabelEmbedding e φ)
        hEPPA block hBlocks hSurj hTrans hTen
        hManyBlocks hNontrivial
    exact Or.inr (Or.inr (Or.inl ⟨φ,hModel,hCases⟩))
  rcases hRest with hRook | hUnequal
  · obtain ⟨φ,hModel⟩ := hRook
    have hEPPA :
        IsEPPAEmbedding rookThreeGraph H
          (EPPAIII.relabelEmbedding e φ) :=
      EPPAIII.eppa_relabel_base G H e heppa φ
        rookThreeGraph hModel
    have hCardV : Fintype.card V = 9 := by
      simpa [rookVertex, Fintype.card_prod] using
        (Fintype.card_congr φ).symm
    have h18 : Fintype.card W = 18 := by omega
    have hCases :=
      rook_eppa_imprimitive_models_up_to_complement
        H (EPPAIII.relabelEmbedding e φ)
        hEPPA block hBlocks hSurj hTrans h18
        hManyBlocks hNontrivial
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨φ,hModel,hCases⟩)))
  · obtain ⟨hCluster,x,y,hDifferent⟩ := hUnequal
    letI : Nonempty V := ⟨x⟩
    obtain ⟨c,φ,hG,hBottom,hHost⟩ :=
      transitive_eppa_unequal_two_cliques_named_host_nonhomogeneous
        G H e heppa block hBlocks hSurj hTrans
        hNonhomogeneous hCluster hManyBlocks hNontrivial
        hDouble x y hDifferent
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨c,φ,hG,hBottom,hHost⟩)))

/-- An explicitly relativized form of the final Proposition 6.17:
assume the *external* Gardiner/cluster base-model implication, not
a hidden axiom or assumption about the host conclusion. -/
theorem imprimitive_actual_host_classification_relative_to_gardiner
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
    (hSourceBase : IsClusterGraph G ∨
      DoubleCover.IsHomogeneousGraph G)
    (hGardinerAndCluster :
      (IsClusterGraph G ∨ DoubleCover.IsHomogeneousGraph G) →
        ImprimitiveBaseModels G) :
    Fintype.card W = 2 * Fintype.card V ∧
      ImprimitiveHostModels G H e :=
  imprimitive_actual_host_classification_of_base_models
    G H e heppa block hBlocks hSurj hTrans
    hNonhomogeneous hManyBlocks hNontrivial hBound
    (hGardinerAndCluster hSourceBase)

end EPPAIII.BlockSystems
