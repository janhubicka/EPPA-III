# Exact named host graphs and Taylor pair matrices

This is the concrete-model companion to the [imprimitive classification](Imprimitive-Classification.md). The main theorem intentionally concludes *named graph equalities* (after explicit equivalences), rather than a vague classification by automorphism groups. The definitions below are **verbatim Lean source fragments**; follow the links to inspect their proofs, decidable instances, and the eventual host-classification lemmas.

## Taylor's balanced pair pattern

A pair of distinct base vertices has four cross/top adjacency bits, with the bottom adjacency fixed by the selected graph. For a nonhomogeneous selected base, the EPPA/block argument eliminates the non-Taylor balanced configurations. Matching between mates of the same fibre is a distinct independent Boolean parameter.

### `PairPattern`
**Source:** [Lean file](../../EPPAIII/DoubleCover/PairPatterns.lean). The exact four-bit record.

```lean
structure PairPattern where
  crossEdge : Bool
  crossNonedge : Bool
  topEdge : Bool
  topNonedge : Bool
  deriving DecidableEq, Repr
```

### `taylor`
**Source:** [Lean file](../../EPPAIII/DoubleCover/PairPatterns.lean). The Taylor choice of those bits (mate edges not included here).

```lean
def taylor : PairPattern :=
  ⟨false, true, true, false⟩
```

### `RepresentsPairPattern`
**Source:** [Lean file](../../EPPAIII/DoubleCover/UniformPattern.lean). What it means for a labelled two-layer graph to realize one uniform pair matrix.

```lean
def RepresentsPairPattern {V : Type*} (G : SimpleGraph V)
    (H : SimpleGraph (Bool × V)) (p : PairPattern) : Prop :=
  (∀ x y : V, x ≠ y → G.Adj x y →
    (H.Adj (false,x) (true,y) ↔ p.crossEdge = true) ∧
    (H.Adj (true,x) (false,y) ↔ p.crossEdge = true) ∧
    (H.Adj (true,x) (true,y) ↔ p.topEdge = true)) ∧
  (∀ x y : V, x ≠ y → ¬ G.Adj x y →
    (H.Adj (false,x) (true,y) ↔ p.crossNonedge = true) ∧
    (H.Adj (true,x) (false,y) ↔ p.crossNonedge = true) ∧
    (H.Adj (true,x) (true,y) ↔ p.topNonedge = true))
```

## Two unequal clique components and the matched host

### `twoCliqueGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/TwoCliqueSwitching.lean). An arbitrary Boolean partition into two cliques, including empty parts.

```lean
def twoCliqueGraph {V : Type*} (color : V → Bool) : SimpleGraph V where
  Adj u v := u ≠ v ∧ color u = color v
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl
```

### `twoCliqueMatchedRel`
**Source:** [Lean file](../../EPPAIII/BlockSystems/TwoCliqueTaylorNamed.lean). The relation between the two enlarged clique components, with optional mate edges.

```lean
def twoCliqueMatchedRel {V : Type*} (c : V → Bool) (mate : Bool)
    (u v : Bool × V) : Prop :=
  u ≠ v ∧
    (Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∨
     (mate = true ∧ u.2 = v.2))
```

### `twoCliqueMatchedGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/TwoCliqueTaylorNamed.lean). The actual simple graph with that adjacency relation.

```lean
def twoCliqueMatchedGraph {V : Type*} (c : V → Bool)
    (mate : Bool) : SimpleGraph (Bool × V) where
  Adj := twoCliqueMatchedRel c mate
  symm := by
    constructor
    intro u v h
    change u ≠ v ∧
      (Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∨
       (mate = true ∧ u.2 = v.2)) at h
    change v ≠ u ∧
      (Bool.xor v.1 (c v.2) = Bool.xor u.1 (c u.2) ∨
       (mate = true ∧ v.2 = u.2))
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with heq | hmate
    · exact Or.inl heq.symm
    · exact Or.inr ⟨hmate.1, hmate.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl
```

## Five-cycle host models

### `cycleFiveExplicitAdjacent`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean). The explicit mod-five adjacency that agrees with Mathlib's C5.

```lean
def cycleFiveExplicitAdjacent (x y : Fin 5) : Prop :=
  x + 1 = y ∨ y + 1 = x

instance : DecidableRel cycleFiveExplicitAdjacent := by
  intro x y
  unfold cycleFiveExplicitAdjacent
  infer_instance
```

### `cycleFiveDoubleRelation`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean). The four possible layer/cross patterns before orbit exclusions.

```lean
def cycleFiveDoubleRelation (topComplement diagonal : Bool)
    (u v : Bool × Fin 5) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then cycleFiveExplicitAdjacent u.2 v.2
    else if topComplement then
      u.2 ≠ v.2 ∧ ¬ cycleFiveExplicitAdjacent u.2 v.2
    else cycleFiveExplicitAdjacent u.2 v.2
  else if u.1 = false then
    u.2 ∈ (if diagonal then
      cycleFiveDiagonalPairShift v.2 else cycleFiveEdgePairShift v.2)
  else
    v.2 ∈ (if diagonal then
      cycleFiveDiagonalPairShift u.2 else cycleFiveEdgePairShift u.2)
```

### `cycleFiveDoubleGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveDoubleClassification.lean). The simple graph built from that relation.

```lean
def cycleFiveDoubleGraph (topComplement diagonal : Bool) :
    SimpleGraph (Bool × Fin 5) :=
  SimpleGraph.fromRel (cycleFiveDoubleRelation topComplement diagonal)

instance (topComplement diagonal : Bool) :
    DecidableRel (cycleFiveDoubleGraph topComplement diagonal).Adj := by
  intro u v
  change Decidable (u ≠ v ∧
    (cycleFiveDoubleRelation topComplement diagonal u v ∨
      cycleFiveDoubleRelation topComplement diagonal v u))
  infer_instance
```

### `cycleFiveDisjointDoubleGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveZeroCrossConclusion.lean). The disjoint union of two five-cycles, a genuine nonhomogeneous EPPA host.

```lean
def cycleFiveDisjointDoubleGraph : SimpleGraph (Bool × Fin 5) where
  Adj u v := u.1 = v.1 ∧
    (SimpleGraph.cycleGraph 5).Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact (SimpleGraph.cycleGraph 5).irrefl h.2
```

### `cycleFiveMatchingRelation`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveMatchingModels.lean). The prism/Petersen matching relation (with top-complement flag).

```lean
def cycleFiveMatchingRelation (topComplement : Bool)
    (u v : Bool × Fin 5) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then cycleFiveExplicitAdjacent u.2 v.2
    else if topComplement then
      u.2 ≠ v.2 ∧ ¬ cycleFiveExplicitAdjacent u.2 v.2
    else cycleFiveExplicitAdjacent u.2 v.2
  else u.2 = v.2

instance (topComplement : Bool) :
    DecidableRel (cycleFiveMatchingRelation topComplement) := by
  intro u v
  unfold cycleFiveMatchingRelation
  infer_instance
```

### `cycleFiveMatchingGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/CycleFiveMatchingModels.lean). The resulting ten-vertex matching graph.

```lean
def cycleFiveMatchingGraph (topComplement : Bool) :
    SimpleGraph (Bool × Fin 5) :=
  SimpleGraph.fromRel (cycleFiveMatchingRelation topComplement)

instance (topComplement : Bool) :
    DecidableRel (cycleFiveMatchingGraph topComplement).Adj := by
  intro u v
  change Decidable (u ≠ v ∧
    (cycleFiveMatchingRelation topComplement u v ∨
     cycleFiveMatchingRelation topComplement v u))
  infer_instance
```

## Three-by-three rook models

### `rookThreeGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/RookThreeBase.lean). The nine-vertex rook graph on a 3×3 grid.

```lean
def rookThreeGraph : SimpleGraph (Fin 3 × Fin 3) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.elim (fun z => Or.inl z.symm) (fun z => Or.inr z.symm)⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

instance : DecidableRel rookThreeGraph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2))
  infer_instance
```

### `rookDoubleRelation`
**Source:** [Lean file](../../EPPAIII/BlockSystems/RookThreeTriangleCertificates.lean). Four possible rook-layer/cross adjacency choices.

```lean
abbrev rookDoubleRelation (topComplement crossNonrook : Bool)
    (u v : Bool × rookVertex) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then rookThreeGraph.Adj u.2 v.2
    else if topComplement then u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2
    else rookThreeGraph.Adj u.2 v.2
  else if crossNonrook then
    u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2
  else rookThreeGraph.Adj u.2 v.2
```

### `rookDoubleGraph`
**Source:** [Lean file](../../EPPAIII/BlockSystems/RookThreeTriangleCertificates.lean). The eighteen-vertex graph built from the chosen rook relation.

```lean
def rookDoubleGraph (topComplement crossNonrook : Bool) :
    SimpleGraph (Bool × rookVertex) :=
  SimpleGraph.fromRel (rookDoubleRelation topComplement crossNonrook)

instance (topComplement crossNonrook : Bool) :
    DecidableRel (rookDoubleGraph topComplement crossNonrook).Adj := by
  intro u v
  change Decidable
    (u ≠ v ∧
      (rookDoubleRelation topComplement crossNonrook u v ∨
       rookDoubleRelation topComplement crossNonrook v u))
  infer_instance
```

## Wagner's eight-vertex exceptional graph

### `wagnerCanonicalGraph`
**Source:** [Lean file](../../EPPAIII/CliqueCovers/WagnerHostConclusion.lean). The exceptional Wagner host for the selected 2K2.

```lean
def wagnerCanonicalGraph : SimpleGraph (CoverVertex 2 2) where
  Adj := wagnerCanonicalAdj
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hx,hy,hi,ha⟩ | ⟨hx,hy,hi,ha⟩ |
      ⟨hx,hy,hcross⟩ | ⟨hx,hy,hcross⟩
    · exact Or.inl ⟨hy,hx,hi.symm,ha.symm⟩
    · exact Or.inr (Or.inl ⟨hy,hx,hi.symm,ha.symm⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hy,hx,hcross⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hy,hx,hcross⟩))
  loopless := by
    constructor
    intro x h
    rcases h with ⟨_,_,_,ha⟩ | ⟨_,_,hi,_⟩ |
      ⟨hf,ht,_⟩ | ⟨ht,hf,_⟩
    · exact ha rfl
    · exact hi rfl
    · exact Bool.false_ne_true (hf.symm.trans ht)
    · exact Bool.false_ne_true (hf.symm.trans ht)
```

## Why the host-model predicates are not themselves sufficiency results

The [exact host disjunction](../../EPPAIII/BlockSystems/ImprimitiveProposition617.lean) uses these canonical graphs. Some of the underlying models are eliminated by EPPA, vertex-transitivity or imprimitivity, and some have independently checked sufficiency constructions. The **global necessity theorem** merely proves that every host under its hypotheses falls in the disjunction. It does not convert an arbitrary parameter choice into an EPPA witness.

In particular: the literal Taylor double has no edges between mates, while `twoCliqueMatchedGraph c true` has a perfect matching between the relevant two complete components; `cycleFiveDisjointDoubleGraph` and its rook counterpart remain nonhomogeneous despite being disjoint doubles of homogeneous bases; the Petersen matching candidate is excluded from the **imprimitive** C5 singleton-cross-degree case by an actual block-invariance argument.

## Which finite cases are proved where

- [C5 low cross-degree conclusion](../../EPPAIII/BlockSystems/CycleFiveSmallCrossConclusion.lean), [C5 complement reduction](../../EPPAIII/BlockSystems/CycleFiveFinalImprimitiveClassification.lean), [Petersen imprimitivity exclusion](../../EPPAIII/BlockSystems/CycleFiveMatchingImprimitive.lean).
- [Rook degree-zero/four conclusion](../../EPPAIII/BlockSystems/RookThreeSmallCrossConclusion.lean), [Rook complement reduction](../../EPPAIII/BlockSystems/RookThreeFinalImprimitiveClassification.lean), [triangle certificates](../../EPPAIII/BlockSystems/RookThreeTriangleCertificates.lean).
- [Two-clique matched host](../../EPPAIII/BlockSystems/TwoCliqueActualTaylorNamed.lean) and [actual imprimitive classification](../../EPPAIII/BlockSystems/Section6NonhomogeneousInterfaces.lean).
- [Wagner sufficiency](../../EPPAIII/CliqueCovers/WagnerSufficiency.lean) is a separate theorem from Wagner necessity.

Return to [the global theorem](Imprimitive-Classification.md) or [Gardiner's exact external premise](Gardiner-External-Assumption.md).
