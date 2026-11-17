# The imprimitive EPPA classification — exact Lean implementation
**Project:** EPPA III · **checked branch:** `formalization/imprimitive-section5-6-integration-20261117` · **main result:** `nonhomogeneous_transitive_imprimitive_eppa_global_classification`.

This page documents the **necessity** direction for an arbitrary finite selected graph and an actual nonhomogeneous vertex-transitive imprimitive EPPA host of at most twice the base order. It contains the **complete top-level Lean source** and the necessary model and predicate declarations copied from the project. Its only external classification premise is Gardiner's theorem **for the selected graph G**, encoded as an ordinary explicit hypothesis. This is neither a proof of Gardiner nor a sufficiency theorem for all candidate hosts.

**Source-of-truth and reproducibility:** [global theorem](../../EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean), [Gardiner bridge](../../EPPAIII/BlockSystems/GardinerLiteralNormalization.lean), [host models](../../EPPAIII/BlockSystems/ImprimitiveProposition617.lean), [axiom checks](../../CheckAxioms.lean). Source snippets below are exact checked-revision excerpts; the full module at the end includes its proof. The exported Lean file, not the wiki copy, is authoritative.

## 1. Read and check the theorem

```lean
import EPPAIII

#check EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
#check EPPAIII.BlockSystems.GeneralImprimitiveHostModels
#check EPPAIII.BlockSystems.ImprimitiveHostModels
#check EPPAIII.BlockSystems.GardinerPublishedModels

#print axioms EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
#print axioms EPPAIII.BlockSystems.imprimitive_actual_host_classification_from_published_gardiner
#print axioms EPPAIII.BlockSystems.gardiner_published_implies_normalized
```

Running `lake build` and `lake env lean CheckAxioms.lean` checks the actual imported declarations. A wiki code block is not a substitute for a Lean run.

## 2. Quantifiers and the mathematical statement

Let `V` be the finite vertex type of `G`, `W` the finite vertex type of `H`, `B` the finite set of block labels, `e : V ↪ W` the fixed chosen embedding, and `block : W → B` the block-label map. The formal hypotheses require all of the following:

1. `IsEPPAEmbedding G H e`: the chosen embedding is induced and every partial automorphism of `G` extends **along that embedding** to an automorphism of `H`.
2. `IsVertexTransitive H`: every ordered pair of vertices of `H` can be related by an automorphism.
3. `InvariantBlockMap H block`, surjectivity of `block`, at least two block labels, and a fibre of size at least two: a genuine **nontrivial automorphism-invariant block system**, not an arbitrary partition of the selected copy.
4. `¬ IsHomogeneousGraph H` and `|W| ≤ 2|V|`.
5. `hGardinerG : IsHomogeneousGraph G → GardinerPublishedModels G`: **exactly one** external implication for this `G`.

The conclusion proves **equality** `|W| = 2|V|` and a disjunction `GeneralImprimitiveHostModels G H e block` of fixed-embedding canonical host models or a Taylor-type pair pattern. No premise says the outside half is already a copy of the selected graph, no canonical coordinates are assumed, and no coherent choice of EPPA extensions is made.

### 2.1 EPPA and graph-homogeneity interfaces

**`IsGraphAutomorphism`** ([source](../../EPPAIII/EPPA/Definitions.lean)). Graph automorphisms preserve both adjacency and nonadjacency.

```lean
def IsGraphAutomorphism {V : Type*} (H : SimpleGraph V)
    (f : Equiv.Perm V) : Prop :=
  ∀ u v : V, H.Adj u v ↔ H.Adj (f u) (f v)
```

**`IsPartialGraphAutomorphism`** ([source](../../EPPAIII/EPPA/Definitions.lean)). Partial bijections are represented by the restriction of a full permutation to a finite domain.

```lean
def IsPartialGraphAutomorphism {V : Type*} (G : SimpleGraph V)
    (D : Finset V) (f : Equiv.Perm V) : Prop :=
  ∀ u v : V, u ∈ D → v ∈ D → (G.Adj u v ↔ G.Adj (f u) (f v))
```

**`IsInducedGraphEmbedding`** ([source](../../EPPAIII/EPPA/Definitions.lean)). The actual distinguished embedding must preserve and reflect adjacency.

```lean
def IsInducedGraphEmbedding {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  ∀ u v : V, G.Adj u v ↔ H.Adj (e u) (e v)
```

**`IsEPPAEmbedding`** ([source](../../EPPAIII/EPPA/Definitions.lean)). The precise extension property does not prescribe coherent choices of host automorphisms.

```lean
def IsEPPAEmbedding {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  IsInducedGraphEmbedding G H e ∧
  ∀ (D : Finset V) (p : Equiv.Perm V),
    IsPartialGraphAutomorphism G D p →
      ∃ (q : Equiv.Perm W),
        IsGraphAutomorphism H q ∧
        ∀ v : V, v ∈ D → q (e v) = e (p v)
```

**`IsHomogeneousGraph`** ([source](../../EPPAIII/DoubleCover/RigidLayerHomogeneity.lean)). Graph homogeneity means every partial automorphism of the graph extends inside the graph itself.

```lean
def IsHomogeneousGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (D : Finset V) (p : Equiv.Perm V),
    IsPartialGraphAutomorphism G D p →
      ∃ σ : Equiv.Perm V,
        IsGraphAutomorphism G σ ∧
        ∀ x : V, x ∈ D → σ x = p x
```

**`IsVertexTransitive`** ([source](../../EPPAIII/BlockSystems/TransitivePartition.lean)). Transitivity is expressed through genuine graph automorphisms.

```lean
def IsVertexTransitive {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ u v : W, ∃ q : Equiv.Perm W,
    IsGraphAutomorphism H q ∧ q u = v
```

**`InvariantBlockMap`** ([source](../../EPPAIII/BlockSystems/Basic.lean)). The equivalence relation of belonging to the same block is invariant under every automorphism.

```lean
def InvariantBlockMap {W B : Type*}
    (H : SimpleGraph W) (block : W → B) : Prop :=
  ∀ (q : Equiv.Perm W), IsGraphAutomorphism H q →
    ∀ w₁ w₂ : W,
      block w₁ = block w₂ ↔ block (q w₁) = block (q w₂)
```

### 2.2 Cluster and cocluster predicates

These are intrinsic `P₃`/co-`P₃` formulations, not a chosen component partition ([source](../../EPPAIII/BlockSystems/ClusterObstructions.lean)).

```lean
def IsClusterGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V,
    G.Adj a b → G.Adj b c → a ≠ c → G.Adj a c
```

```lean
def IsCoClusterGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V,
    a ≠ b → b ≠ c → a ≠ c →
    ¬ G.Adj a b → ¬ G.Adj b c → ¬ G.Adj a c
```

## 3. Exact predicates naming the possible hosts

### 3.1 Fixed relabelling of canonical bases

`CanonicalBaseCopy K G φ` means that the graph `K` becomes **exactly** the selected graph `G` after transporting adjacency along the stated equivalence `φ`. The reindexed selected embedding is always carried through to the host, rather than forgotten.

```lean
def CanonicalBaseCopy {U V : Type*}
    (K : SimpleGraph U) (G : SimpleGraph V) (φ : U ≃ V) : Prop :=
  ∀ x y : U, K.Adj x y ↔ G.Adj (φ x) (φ y)
```

### 3.2 Uniform clique unions, generalized covers, and Wagner

Canonical clique-cover vertices have a side bit, a clique number, and a within-clique coordinate. `CrossType` lists the four diagonal inter-side relations, and a Boolean parameter specifies all cross-clique edges. These are definitions of candidate graphs, not assertions that every parameter choice is EPPA. [source](../../EPPAIII/CliqueCovers/Basic.lean)

```lean
inductive CrossType where
  | empty
  | full
  | matching
  | coMatching
  deriving DecidableEq, Repr
```

```lean
abbrev CoverVertex (s t : Nat) := Bool × (Fin s × Fin t)
```

```lean
def coverAdj {s t : Nat} (X : CrossType) (Y : Bool)
    (x y : CoverVertex s t) : Prop :=
  (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 ≠ y.1 ∧
    if x.2.1 = y.2.1 then X.rel x.2.2 y.2.2 else Y = true)
```

```lean
def cliqueUnion (s t : Nat) : SimpleGraph (Fin s × Fin t) where
  Adj := fun x y => x.1 = y.1 ∧ x.2 ≠ y.2
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro x h
    exact h.2 rfl
```

The canonical construction `coverGraph` packages `coverAdj` into an undirected loopless `SimpleGraph`:

```lean
def coverGraph (s t : Nat) (X : CrossType) (Y : Bool) :
    SimpleGraph (CoverVertex s t) where
  Adj := coverAdj X Y
  symm := by
    constructor
    intro x y h
    exact coverAdj_flip X Y x y h
  loopless := by
    constructor
    intro x h
    exact coverAdj_irrefl X Y x h
```

The conclusion for an equal-clique base is a fixed-embedding generalized cover **or** an explicit Wagner exception:

```lean
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
```

### 3.3 Five-cycle and 3×3 rook host alternatives

The exceptional pattern predicates preserve the fixed bottom embedding. The C₅ cases include the disjoint double `2C₅`; the rook cases include `2R₃`. Neither is to be discarded as homogeneous. For complementary cases, the host and selected graph are complemented **together** and then the selected vertices are relabelled by a concrete self-complementing equivalence.

```lean
def CycleFiveSmallHostPatterns {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 5) ↪ W) : Prop :=
    (∃ φ : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveDisjointDoubleGraph) ∨
    (∃ φ : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveMatchingGraph false) ∨
    (∃ (φ : Bool × Fin 5 ≃ W) (diagonal : Bool),
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveDoubleGraph false diagonal)
```

```lean
def RookSmallHostPatterns {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : rookVertex ↪ W) : Prop :=
    (∃ φ : Bool × rookVertex ≃ W,
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDisjointDoubleGraph) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (topComplement : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookMatchingGraph topComplement) ∨
    (∃ (φ : Bool × rookVertex ≃ W) (crossNonrook : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDoubleGraph false crossNonrook)
```

### 3.4 Proposition 6.17 model predicate

The five alternatives below correspond to homogeneous/cluster bases: equal-clique cover or Wagner, their complements, C₅ exceptions, rook exceptions, or the exact unequal two-clique matched double. All host equalities are made in canonical coordinates fixing `e`.

```lean
def ImprimitiveHostModels {V W : Type*} [Fintype V] [Fintype W]
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
```

### 3.5 The arbitrary-base extension

Outside the special base types the theorem gives a **Taylor inter-fibre pattern**, with `mate : Bool` allowing uniform mate edges (present or absent), plus orbit transitivity for ordered vertex pairs lying in different imprimitivity blocks. It would be incorrect to silently erase the mate-edge Boolean and claim every host is the literal mate-free Taylor double.

```lean
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
```

## 4. The Gardiner assumption occurs as a term parameter

The literal published-form input is the following six-case disjunction. It is **not** introduced by `axiom` or `sorry`. The global theorem takes an implication whose domain is homogeneity of **this** `G`. See [the Gardiner page](Gardiner-External-Assumption.md) for its complete normalization and precise trust boundary.

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

## 5. Complete actual Lean source of the main theorem

The following is the **verbatim** `ImprimitiveGlobalClassification.lean` module from the documented branch, including imports, the complete output predicate, the theorem's exact hypotheses, and its entire Lean proof. The imported support theorems are linked in the dependency map in §6; reproducing them inline would duplicate the rest of the research library.

```lean
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
assumed. Gardiner is invoked only for G itself: the complement
branch is reached after G is proved non-homogeneous, so its
complement is non-homogeneous too.

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
    (hGardinerG : DoubleCover.IsHomogeneousGraph G →
      GardinerPublishedModels G) :
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
        hGardinerG
    exact Or.inl hCases.2
  by_cases hCluster : IsClusterGraph G
  · have hCases :=
      imprimitive_actual_host_classification_from_published_gardiner
        G H e heppa block hBlocks hSurj hTrans hNonhomogeneousH
        hManyBlocks hNontrivial hBound (Or.inr hCluster)
        hGardinerG
    exact Or.inl hCases.2
  by_cases hCoCluster : IsCoClusterGraph G
  · have hNonHomogeneousCBase :
        ¬ DoubleCover.IsHomogeneousGraph Gᶜ :=
      (DoubleCover.nonhomogeneous_complement_iff G).mp hHom
    have hClusterC : IsClusterGraph Gᶜ := by
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
        (Or.inr hClusterC)
        (fun hHomC => (hNonHomogeneousCBase hHomC).elim)
    exact Or.inr (Or.inl hCases.2)
  · have hTaylor :=
      transitive_eppa_double_cover_classification
        G H e heppa block hTrans hBlocks hSurj
        hHom hCluster hCoCluster hManyBlocks hNontrivial hDouble
    exact Or.inr (Or.inr hTaylor)

end EPPAIII.BlockSystems
```

## 6. How the proof works

### Step A — rule out strict inequality

`nonhomogeneous_imprimitive_eppa_host_exactly_double` uses the small-host ordered-pair orbit theorem. When `|W| < 2|V|`, a transitive EPPA host has the required ordered-edge and ordered-nonedge orbits. An invariant nontrivial block equivalence must then agree with adjacency or with nonadjacency away from the diagonal. Such a transitive graph is a uniform union of cliques or its complement, hence homogeneous. The assumed nonhomogeneity forces `|W|=2|V|`. This is *not* an appeal to a bare assertion that the host is connected.

Key sources: [strict order](../../EPPAIII/BlockSystems/ImprimitiveStrictOrder.lean), [small host pair orbits](../../EPPAIII/BlockSystems/SmallHostRankThreeFinal.lean), [imprimitive rank-three homogeneity](../../EPPAIII/BlockSystems/RankThreeActualImprimitiveBlocks.lean).

### Step B — the selected base is homogeneous

An external term `hGardinerG hHom` supplies a *concrete* graph equivalence to one of Gardiner's six finite homogeneous models. `gardiner_published_implies_normalized` uses explicitly proved C₅ and rook self-complementarity to reduce to four normalized model types. `imprimitive_actual_host_classification_of_base_models` then transports the **actual** induced EPPA embedding through the equivalence and invokes the separate classified equal-clique/Wagner, C₅, and rook host theorems. The external input is only the **classification of the base graph**, not a prepackaged host classification.

Key sources: [literal Gardiner normalization](../../EPPAIII/BlockSystems/GardinerLiteralNormalization.lean), [source bridge](../../EPPAIII/BlockSystems/ImprimitiveGardinerBridge.lean), [actual-host Proposition 6.17](../../EPPAIII/BlockSystems/ImprimitiveProposition617.lean).

### Step C — the base is a cluster but not homogeneous

The elementary checked lemma `cluster_homogeneous_or_unequal_degrees` says a cluster graph either is homogeneous (uniform clique sizes) or has vertices of different degrees. In the latter case the full unequal-clique host proof forces exactly two base clique components of different sizes, and shows that the transitive host is two complete graphs joined by a perfect matching. The difficult `k_i+k_j=m` equality is derived by symmetric cross-block degree counting, not by unsupported regularity intuition.

Key sources: [regular cluster is homogeneous](../../EPPAIII/BlockSystems/ClusterRegularHomogeneity.lean), [actual two-block conclusion](../../EPPAIII/BlockSystems/UnequalCase1TwoBlocks.lean), [double-counting equation](../../EPPAIII/BlockSystems/CrossBlockSizeEquation.lean), [matching conclusion](../../EPPAIII/BlockSystems/UnequalCase1Matching.lean), [named host](../../EPPAIII/BlockSystems/Section6NonhomogeneousInterfaces.lean).

### Step D — the base is a cocluster

Pass to `(Gᶜ,Hᶜ)` using checked complement transport of EPPA, vertex transitivity, block invariance, and host nonhomogeneity. The cocluster assumption becomes a cluster assumption for `Gᶜ`. Crucially, earlier case splits already show `G` nonhomogeneous. Hence `Gᶜ` is nonhomogeneous too: the temporary Gardiner premise required by the reusable cluster theorem is discharged by contradiction, **without assuming Gardiner again for `Gᶜ`**. This is the premise-minimality simplification of [PR #398](https://github.com/janhubicka/EPPA-III/pull/398).

### Step E — neither homogeneous, cluster, nor cocluster

The two-point EPPA/block argument proves the chosen base meets every block exactly once and all blocks have size two. A canonical equivalence `Bool × V ≃ W`, fixed on the actual selected copy, is **constructed**. The pair-pattern theorem eliminates the non-Taylor balanced inter-fibre possibilities for a nonhomogeneous base; mate edges remain uniformly optional. The ordered inter-block edge and nonedge orbit result is transported back to the original vertex type `W`. No coherent system of EPPA lifts is assumed.

Key sources: [partition and double-counting](../../EPPAIII/BlockSystems/TransitivePartition.lean), [optional-mate Taylor classification](../../EPPAIII/DoubleCover/CompleteTaylor.lean), [actual ordered orbit transfer](../../EPPAIII/BlockSystems/OrderedInterblockOrbits.lean), [case assembly](../../EPPAIII/BlockSystems/ImprimitiveClassification.lean).

## 7. Dependencies and scope of the certificate

| Statement or dependency | Lean source | What is actually proved |
|---|---|---|
| Exact-order reduction | [ImprimitiveStrictOrder](../../EPPAIII/BlockSystems/ImprimitiveStrictOrder.lean) | Nonhomogeneous imprimitive small host has exactly double the order |
| Actual-host Proposition 6.17 | [ImprimitiveProposition617](../../EPPAIII/BlockSystems/ImprimitiveProposition617.lean) | Host models when a selected canonical base model is supplied |
| Gardiner literal → normalized | [GardinerLiteralNormalization](../../EPPAIII/BlockSystems/GardinerLiteralNormalization.lean) | Checked finite graph equivalences and model implication |
| Gardiner classification itself | **External mathematical theorem** | Supplied as `hGardinerG`; **not** proved in this repository |
| Global imprimitive necessity | [ImprimitiveGlobalClassification](../../EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean) | One disjunction for arbitrary selected base graph, fixed `e` and `block` |
| Internal all-transversals/two-graph equivalence | [FourWayAllOrders](../../EPPAIII/TwoGraphs/FourWayAllOrders.lean) | Checked equivalence in the Taylor setting |
| Complete finite homogeneous two-graph 6/10 list | **External classification** | Not required by global necessity; needed to turn candidate Taylor patterns into the final manuscript's finite list |
| Sufficiency of all listed models | Separate constructions/cases | **Not** asserted by the global necessity theorem |
| Printed proof as written | TeX review | The Lean alternative does not itself repair invalid English invocations |

### Known printed-proof discrepancies that must remain visible

- **Claim 5.14:** the maximal-domain extension step in the printed proof does not establish adjacency preservation. Lean uses a different invariant-pair argument.
- **Claim 5.15:** its conclusion follows from the alternative two-point pair-matrix proof; it does not validate the printed dependence on Claim 5.14.
- **Unequal-clique Case 1:** require a proof of positive common cross-block degree and `k_i+k_j=m`, followed by the connected-component/matching argument. Regularity alone does not classify the bipartite graph.
- **Proposition 6.17:** the printed equal-clique lemma is invoked without establishing an outside-half hypothesis; the stronger Lean theorem has no such hypothesis. The text also needs the `2G` alternative stated correctly.
- **Two invariant clique blocks** do not imply two maximal cliques (the triangular prism has further maximal cliques).

### Exact CI scope

[PR #396](https://github.com/janhubicka/EPPA-III/pull/396) compiled the global theorem and passed its axiom audit; [PR #398](https://github.com/janhubicka/EPPA-III/pull/398) passed after weakening Gardiner to the single exact premise. In that run, the audit checked 1,070 declarations and reported only standard logical axioms. [PR #397](https://github.com/janhubicka/EPPA-III/pull/397) checked the internal two-graph equivalences. [PR #400](https://github.com/janhubicka/EPPA-III/pull/400) integrates the previously checked Section 5/6 modules into one import/axiom audit; consult its **latest exact-head** CI before claiming the combined branch passed. An external classification being an explicit theorem parameter is not an unexpected axiom, but it remains a mathematical assumption.

## 8. Rebuild and inspect the full proof

From a checkout of the integrated branch, with the `lean-toolchain` and `lakefile` from the repository:

```lean
lake build
lake env lean CheckAxioms.lean

# In an extra Lean scratch file:
import EPPAIII
#check EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
#print axioms EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
```

For changes to the published classification, review both the exact Lean statement and the manuscript separately. Do not remove manuscript `TODO` or proof-gap markers solely because a different formal proof is available.

See [Gardiner's exact external premise](Gardiner-External-Assumption.md) and [publication setup](Publishing.md).
