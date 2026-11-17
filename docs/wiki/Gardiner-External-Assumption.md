# Gardiner's theorem — how the external classification is represented in Lean

**Purpose.** This page gives the precise Lean meaning of the Gardiner input to the EPPA III imprimitive-host necessity theorem. It separates (i) the **external classification of finite homogeneous graphs**, represented as a hypothesis, from (ii) the **internally proved normalization and host-classification deductions**.

The source is [GardinerLiteralNormalization.lean](../../EPPAIII/BlockSystems/GardinerLiteralNormalization.lean), [ImprimitiveGardinerBridge.lean](../../EPPAIII/BlockSystems/ImprimitiveGardinerBridge.lean), and [ImprimitiveGlobalClassification.lean](../../EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean). All code excerpts below are copied from the documented branch; source files are authoritative.

## 1. The **exact six-case** predicate

Finite homogeneous graphs are described by a union of equal-size cliques, its complement, the five-cycle, its complement, the 3×3 rook graph, or its complement. The models are witnessed by **explicit graph-equivalence maps**; a name such as `C₅` is not treated as equality of graphs on unrelated vertex types.

The core transport predicate is:

```lean
def CanonicalBaseCopy {U V : Type*}
    (K : SimpleGraph U) (G : SimpleGraph V) (φ : U ≃ V) : Prop :=
  ∀ x y : U, K.Adj x y ↔ G.Adj (φ x) (φ y)
```

The literal, unnormalized six-case Gardiner conclusion is:

```lean
def GardinerPublishedModels {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t) G φ) ∨
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t)ᶜ G φ) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G φ) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5)ᶜ G φ) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G φ) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraphᶜ G φ)
```

The first two disjuncts have `0 < s` and `0 < t`. Thus this **literal model predicate only covers nonempty canonical bases**. The global imprimitive theorem does not presume a universal `∀ G` Gardiner statement on an empty vertex type: the actual nontrivial host block system and `|H| ≤ 2|G|` already force the selected graph to have positive order.

## 2. The actual external hypothesis of the global theorem

In [the checked global theorem](../../EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean) the *only* Gardiner parameter is exactly:

```lean
(hGardinerG : DoubleCover.IsHomogeneousGraph G →
  GardinerPublishedModels G)
```

That is an ordinary **term argument to a theorem**. There is **no** `axiom Gardiner`, `sorry`, `admit`, implicit `Classical.choice` proof of Gardiner, or hidden hypothesis asserting a candidate host model. Using `hGardinerG hHom` is valid Lean reasoning **relative to this external input**; it is not a kernel proof of the external graph-classification theorem.

Equivalently, in mathematical language the principal result says: for the chosen finite graph `G`, **if** every finite homogeneous `G` of this size has one of the six Gardiner forms, **then** every nonhomogeneous transitive imprimitive EPPA host of `G` of size at most `2|G|` has one of the explicitly described canonical or Taylor host patterns.

The assumption concerns only `G`, not all graphs `K : SimpleGraph V` and not `Gᶜ` separately. This premise reduction was checked in [PR #398](https://github.com/janhubicka/EPPA-III/pull/398).

## 3. Normalization: six published forms to four canonical forms

The canonical host classification needs only four base forms: equal-clique union, its complement, `C₅`, and rook `R₃`. The other two printed Gardiner alternatives are not assumed away: the equivalences are proved concretely.

### The four-form predicate

```lean
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
```

### Five-cycle self-complementarity

The permutation `cycleFiveDoubleIndex` (multiplication by two modulo five) identifies the complement of the cycle with the cycle itself. Composing that equivalence with the selected graph relabelling preserves the fixed embedding.

```lean
theorem gardiner_complement_cycle_normalized
    {V : Type*} (G : SimpleGraph V)
    (φ : Fin 5 ≃ V)
    (hModel : CanonicalBaseCopy
      (SimpleGraph.cycleGraph 5)ᶜ G φ) :
    ∃ ψ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G ψ := by
  let ψ : Fin 5 ≃ V := cycleFiveDoubleIndex.trans φ
  refine ⟨ψ,?_⟩
  intro x y
  have hSelf :
      (SimpleGraph.cycleGraph 5).Adj x y ↔
        ((SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex).Adj x y := by
    rw [cycleFiveComplementIndex_comap_back]
  calc
    (SimpleGraph.cycleGraph 5).Adj x y ↔
        ((SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex).Adj x y :=
      hSelf
    _ ↔ G.Adj (ψ x) (ψ y) := by
      simpa [ψ, Equiv.trans_apply] using
        hModel (cycleFiveDoubleIndex x) (cycleFiveDoubleIndex y)
```

### 3×3 rook self-complementarity

`rookComplementIndex` is an explicit bijective linear coordinate change on the nine rook vertices; the required complement-adjacency transport is a checked Lean theorem. Again the selected base equivalence is composed, not silently discarded.

```lean
theorem gardiner_complement_rook_normalized
    {V : Type*} (G : SimpleGraph V)
    (φ : rookVertex ≃ V)
    (hModel : CanonicalBaseCopy rookThreeGraphᶜ G φ) :
    ∃ ψ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G ψ := by
  let ψ : rookVertex ≃ V := rookComplementIndex.trans φ
  refine ⟨ψ,?_⟩
  intro x y
  have hSelf :
      rookThreeGraph.Adj x y ↔
        (rookThreeGraphᶜ.comap rookComplementIndex).Adj x y := by
    rw [rookComplementIndex_comap_back]
  calc
    rookThreeGraph.Adj x y ↔
        (rookThreeGraphᶜ.comap rookComplementIndex).Adj x y :=
      hSelf
    _ ↔ G.Adj (ψ x) (ψ y) := by
      simpa [ψ, Equiv.trans_apply] using
        hModel (rookComplementIndex x) (rookComplementIndex y)
```

### The complete checked six-to-four normalization proof

```lean
theorem gardiner_published_implies_normalized
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : GardinerPublishedModels G) :
    GardinerHomogeneousModels G := by
  rcases h with hEqual | hRest
  · exact Or.inl hEqual
  rcases hRest with hComplement | hRest
  · exact Or.inr (Or.inl hComplement)
  rcases hRest with hCycle | hRest
  · exact Or.inr (Or.inr (Or.inl hCycle))
  rcases hRest with hCycleComplement | hRest
  · obtain ⟨φ,hModel⟩ := hCycleComplement
    obtain ⟨ψ,hψ⟩ :=
      gardiner_complement_cycle_normalized G φ hModel
    exact Or.inr (Or.inr (Or.inl ⟨ψ,hψ⟩))
  rcases hRest with hRook | hRookComplement
  · exact Or.inr (Or.inr (Or.inr hRook))
  · obtain ⟨φ,hModel⟩ := hRookComplement
    obtain ⟨ψ,hψ⟩ :=
      gardiner_complement_rook_normalized G φ hModel
    exact Or.inr (Or.inr (Or.inr ⟨ψ,hψ⟩))
```

**What has been proved here:** every witness to the literal six-case `GardinerPublishedModels G` provides a witness to `GardinerHomogeneousModels G`. **What has not:** `GardinerPublishedModels G` from the homogeneity of `G` without being supplied Gardiner as an input.

## 4. Why a general union of cliques needs a fifth base model

The manuscript's Proposition 6.17 also allows `G` to be a union of cliques whose component sizes are not equal. Such a graph is generally **not** homogeneous. The formal proof therefore separates the Gardiner alternatives from the elementary unequal-degree cluster alternative:

```lean
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
```

A finite cluster graph with equal degrees is homogeneous. Contrapositively, a nonhomogeneous cluster graph has vertices with different degrees. This is a **Lean theorem**, not another invocation of Gardiner:

```lean
theorem cluster_homogeneous_or_unequal_degrees
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hCluster : IsClusterGraph G) :
    DoubleCover.IsHomogeneousGraph G ∨
      ∃ x y : V,
        (DoubleCover.clusterBaseNeighbours G x).card ≠
          (DoubleCover.clusterBaseNeighbours G y).card := by
  classical
  by_cases hEqual : ∀ x y : V,
      (DoubleCover.clusterBaseNeighbours G x).card =
        (DoubleCover.clusterBaseNeighbours G y).card
  · exact Or.inl (cluster_equal_degrees_isHomogeneous G hCluster hEqual)
  · right
    push_neg at hEqual
    exact hEqual
```

The bridge uses Gardiner only in the homogeneous branch; the unequal-degree branch is an elementary graph-theoretic conclusion.

```lean
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
```

## 5. Fully formal host statement for the homogeneous-or-cluster subcase

Before extending to an arbitrary selected graph, the formalization proves Proposition 6.17 **relative to exactly the published-form Gardiner implication**. Here is the complete source declaration and its proof application:

```lean
theorem imprimitive_actual_host_classification_from_published_gardiner
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
    (hGardinerPublished : DoubleCover.IsHomogeneousGraph G →
      GardinerPublishedModels G) :
    Fintype.card W = 2 * Fintype.card V ∧
      ImprimitiveHostModels G H e :=
  imprimitive_actual_host_classification_from_gardiner
    G H e heppa block hBlocks hSurj hTrans hNonhomogeneous
    hManyBlocks hNontrivial hBound hSource
    (fun hHom => gardiner_published_implies_normalized
      G (hGardinerPublished hHom))
```

This theorem proves **host order exactly doubled** and `ImprimitiveHostModels G H e`. It requires the usual actual EPPA embedding, transitivity, nontrivial invariant blocks, nonhomogeneous host, size bound, and `hSource : IsHomogeneousGraph G ∨ IsClusterGraph G`. The only imported *classification* is Gardiner, and only for the given base `G`. The named host alternatives are separately established from genuine EPPA in [ImprimitiveProposition617.lean](../../EPPAIII/BlockSystems/ImprimitiveProposition617.lean), not assumed as a consequence of Gardiner.

## 6. Why the global cocluster branch does not require Gardiner for the complement

The global theorem first branches on homogeneity of `G` and whether `G` is a cluster. It reaches the cocluster branch with `hHom : ¬ IsHomogeneousGraph G`. The checked lemma `nonhomogeneous_complement_iff` yields `¬ IsHomogeneousGraph Gᶜ`. Therefore, if a reused classification theorem has an argument `IsHomogeneousGraph Gᶜ → GardinerPublishedModels Gᶜ`, it is proved immediately by contradiction. The actual code is:

```lean
have hNonHomogeneousCBase :
    ¬ DoubleCover.IsHomogeneousGraph Gᶜ :=
  (DoubleCover.nonhomogeneous_complement_iff G).mp hHom
-- ...
(Or.inr hClusterC)
(fun hHomC => (hNonHomogeneousCBase hHomC).elim)
```

This apparently small simplification matters: it prevents the completed theorem from accidentally smuggling in a universal Gardiner scheme or an extra assumption about the complement.

## 7. Trust boundary and accuracy checklist

| Claim | Status |
|---|---|
| Graph homogeneity and canonical model predicates are formally defined | Lean definitions |
| The six-case Gardiner theorem itself | **External**; premise `hGardinerG`, not proved in Lean |
| Self-complementarity of `C₅` and 3×3 rook model | Checked graph equivalences |
| Six published cases imply four normalized cases | Lean theorem, verified |
| Every regular cluster graph is homogeneous | Lean theorem, verified |
| The source-facing homogeneous/cluster host classification | Lean theorem **relative to Gardiner** |
| Arbitrary-base imprimitive necessity | Lean theorem **relative to Gardiner** |
| Finite homogeneous **two-graph** classification (trivial, 6/10-point cases) | Separate external mathematical input for the sharp Taylor list |
| Sufficiency of every item of the canonical disjunction | Not supplied by the global necessity theorem |

### Reproduce the checked interfaces
These commands inspect the **actual declarations and axioms** at the Git revision; they do not assert the external classification theorem:

```lean
import EPPAIII

#check EPPAIII.BlockSystems.GardinerPublishedModels
#check EPPAIII.BlockSystems.GardinerHomogeneousModels
#check EPPAIII.BlockSystems.ImprimitiveBaseModels
#check EPPAIII.BlockSystems.gardiner_complement_cycle_normalized
#check EPPAIII.BlockSystems.gardiner_complement_rook_normalized
#check EPPAIII.BlockSystems.gardiner_published_implies_normalized
#check EPPAIII.BlockSystems.imprimitive_base_models_from_gardiner
#check EPPAIII.BlockSystems.imprimitive_actual_host_classification_from_published_gardiner
#check EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification

#print axioms EPPAIII.BlockSystems.gardiner_published_implies_normalized
#print axioms EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
```

[PR #395](https://github.com/janhubicka/EPPA-III/pull/395) passed exact-head Lean CI for the literal six-to-four normalization; [PR #396](https://github.com/janhubicka/EPPA-III/pull/396) and [PR #398](https://github.com/janhubicka/EPPA-III/pull/398) verified the global theorem and its minimal-premise simplification. The external Gardiner premise must remain visible in any summary or manuscript validation mark.

Return to the [complete imprimitive theorem and proof](Imprimitive-Classification.md).
