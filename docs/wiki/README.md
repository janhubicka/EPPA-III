# EPPA III — Lean formalization wiki

This wiki documents the formalization in [`janhubicka/EPPA-III`](https://github.com/janhubicka/EPPA-III) of **small vertex-transitive EPPA witnesses**, including the global imprimitive necessity theorem and the conditional fixed-embedding classification of the full main result.

The principal certified result is a **necessity theorem** for nonhomogeneous hosts of at most twice the base order. It constructs the host alternatives using the actual selected embedding, an actual invariant block partition, and a **single explicit external Gardiner premise for the selected base**. The premise is an input to the Lean theorem, not a Lean proof of Gardiner's classification.

## Read the documentation

| Page | What it contains |
|---|---|
| [Imprimitive classification — exact Lean code and proof architecture](Imprimitive-Classification.md) | The EPPA and block-system definitions, exact model predicates, full main Lean module, proof-by-cases, dependency map, and source-fidelity audit |
| [Gardiner: formal external hypothesis and normalization](Gardiner-External-Assumption.md) | Literal six-case definition, graph relabelling, C₅/rook self-complementarity, reduction to canonical cases, and the precise trust boundary |
| [Named host models and Taylor matrices](Named-Host-Models.md) | Exact Lean definitions for all terminal canonical graph constructors appearing in the host alternatives |
| [Primitive classification](Primitive-classification.md) | The full main theorem, fixed-embedding Lean endpoint, and November 19 adversarial statement-to-Lean correspondence audit |
| [Primitive classification inputs](Primitive-classification-assumptions.md) | External rank-three catalogue, local recognition, and finite computations |
| [Publishing this wiki](Publishing.md) | The GitHub Actions sync from `docs/wiki/` to the separate Wiki Git repository, initialization, and troubleshooting |

## Runnable entry points

```lean
import EPPAIII

#check EPPAIII.BlockSystems.nonhomogeneous_transitive_imprimitive_eppa_global_classification
#check EPPAIII.BlockSystems.GeneralImprimitiveHostModels
#check EPPAIII.BlockSystems.ImprimitiveHostModels
#check EPPAIII.BlockSystems.GardinerPublishedModels
#check EPPAIII.BlockSystems.gardiner_published_implies_normalized
#check EPPAIII.BlockSystems.imprimitive_actual_host_classification_from_published_gardiner
#check EPPAIII.BlockSystems.transitive_eppa_double_cover_classification
#check EPPAIII.BlockSystems.nonhomogeneous_imprimitive_eppa_host_exactly_double
```

Run `lake build` and `lake env lean CheckAxioms.lean` in the same Git revision.

## What is and is not certified

The [global necessity theorem](../../EPPAIII/BlockSystems/ImprimitiveGlobalClassification.lean) and its Gardiner-interface simplification have passed exact-head Lean CI on [PR #396](https://github.com/janhubicka/EPPA-III/pull/396) and [PR #398](https://github.com/janhubicka/EPPA-III/pull/398). The two-graph internal equivalence is in [PR #397](https://github.com/janhubicka/EPPA-III/pull/397). [PR #400](https://github.com/janhubicka/EPPA-III/pull/400) combines those previously checked sources into a unified Section 5/6 import and axiom audit.

**The conditional fixed-embedding equivalence is separately assembled in `EPPAIII/Primitive/PublishedRecognitionAssembly.lean`, with explicit published recognition and finite-check inputs. Do not substitute the global imprimitive necessity theorem for a proof of Gardiner, the rank-three classification, an unconditional finite computation, or validation of each originally printed English argument.** The paper's gaps in Claim 5.14, unequal-clique counting, and Proposition 6.17 require separate source-level repairs.

The maintained pages live under `docs/wiki/`; the automated Wiki tab is a synchronized publication target, not the source of truth.
