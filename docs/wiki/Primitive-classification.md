# Primitive EPPA witness classification

## Manuscript statement

Let `H` be a finite simple graph whose full automorphism group acts transitively on vertices. Fix a finite simple graph `G` and a particular induced embedding `e : G ↪ H`. Suppose `|V(H)| ≤ 2|V(G)|`. The classification in the 19 November 2026, 14:37 manuscript, `thmintro:classification`, asserts that `IsEPPAEmbedding G H e` is equivalent to the following list, with simultaneous complementation of both graphs permitted.

| Case | Host and selected graph |
|---|---|
| 1 | A homogeneous host, with any induced selection. Gardiner's list gives `C₅`, `R₃`, and equal-sized disjoint clique unions, together with their complements. |
| 2 | `T(n)` for `n ≥ 5`, with the selected graph the line graph of a triangle-free graph on `n` points. The Lean target formulates triangle-freeness for the selected edges in the given host embedding. The passage to abstract line-graph isomorphism is a separate step. |
| 3(a) | Exact doubled order, with a homogeneous selected graph and host its disjoint double or Taylor double. |
| 3(b) | Exact doubled order, with an equal-sized disjoint clique union and a generalised clique cover of it. |
| 3(c) | Exact doubled order, with two selected cliques of distinct sizes and the host two cliques of the total selected order joined by a perfect matching. |
| 4(a–f) | Wagner / `2K₂`. `C₅` prism / `C₅`. Complement of the 2-clique extension of `C₅` / `C₅`. `R₃` prism / `R₃`. `R₃ ⊔ complement(R₃)`, with corresponding vertices joined by a matching / `R₃`. Complement of the 2-clique extension of `R₃` / `R₃`. |
| 4(g–k) | Icosahedron / the four stated six-vertex forms. `R₄` / induced subgraph of `R₃ ⊔ K₁` or `L₄,₂`. Clebsch / induced subgraph of a listed figure model. `J(6,3)` / a Petersen switching mate. Schläfli / induced subgraph of a listed figure model. |

The table describes the full manuscript statement. The corresponding-vertex matching in Case 4(e) is present in the 19 November 14:37 manuscript. It is a graph isomorphism from the lower rook graph to the **complement of the upper anti-rook graph**; an arbitrary matching would be false. This corresponds to `rookMatchingGraph true` (with the selected embedding fixed).
The primitive Lean equivalence retains the specific embedding. Its alternatives are the homogeneous hosts,
triangle-free selections in triangular hosts, and the R4, Clebsch and
Schläfli figure cases. Each finite figure clause places the actual
selection in a listed model by a host isomorphism.
The [full fixed-embedding equivalence](https://github.com/janhubicka/EPPA-III/blob/main/EPPAIII/Primitive/SmallWitnessNamedClassification.lean)
combines these with the imprimitive cases and the icosahedral and Johnson Taylor
transversals.

## How the primitive proof connects

1. The exact small-host trichotomy gives a complete graph, an edgeless graph, or a rank-three full automorphism action. Its conditional primitivity hypothesis is needed at exact doubled order. The homogeneous and imprimitive cases are discharged separately.
2. In a rank-three host, an automorphism fixing a selected vertex preserves the neighbours and the distinct non-neighbours. Extending a partial map while fixing that vertex transports EPPA to the selected vertices in each part.
3. The two parts and the selected vertex partition the host. Cardinality forces a part with at least half of its vertices selected. Both parts are transitive and strictly smaller, allowing the minimal-counterexample argument to invoke the **pair** classification. Using the host alone discards information needed in the stabilizer argument.
4. The rank-three catalogue identifies the ambient graph. Subconstituent identifications, parameter screens, local action bounds, finite checks and family exclusions are separate obligations. Complementation interchanges the two parts.
5. The final theorem needs both the necessity argument and the positive witness constructions or exact positive finite checks. Neither the trichotomy nor the catalogue supplies that equivalence.

The rank-three assumptions and finite computation boundary are listed on the [assumptions page](Primitive-classification-assumptions).

## Verification status

The endpoint `primitiveCases_iff_eppa_of_publishedRankThreeCoverage`
proves the equivalence for the specified embedding in a finite primitive host.
The proof includes all rank-two polar reductions and all 40 extraspecial and
exceptional affine reductions. Exhaustive model recognition, the separate
local recognition hypotheses, the four small Paley exclusions, and the
specified finite outcomes are explicit theorem parameters. The order-40
rooted certificate is part of the corresponding model data. [Lean endpoint](https://github.com/janhubicka/EPPA-III/blob/main/EPPAIII/Primitive/PublishedRankThreeCoverage.lean#L98)

## Local checks

The repository pins Lean in `lean-toolchain` and mathlib in `lakefile.toml`. Run `lake build`, then:

```bash
lake env lean CheckAxioms.lean > axioms.log 2>&1
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean
```

The axiom check detects proof dependencies introduced through Lean axioms. To audit explicit theorem parameters such as an external classifier, also inspect the theorem types. Progress on the primitive part is recorded in the validation directory.

## Adversarial main-theorem correspondence audit — 19 November 2026

**Manuscript audited:** `main-new(20261119-143746).tex`, SHA-256 `3d625213b98f8c839d23373eaf130b1fd44862397c5338fbf27e0d2c25b332e0`.
**Formal baseline:** repository `main`, commit `73975a93c441db090f1845906e0a230f66ec3973`.
The paper states a classification for a **chosen induced subgraph** of a vertex-transitive host, with simultaneous complementation. The Lean endpoint
[`smallWitnessNamedModelCases_iff_eppa_of_published_sources`](../../EPPAIII/Primitive/PublishedRecognitionAssembly.lean)
uses a **specific induced embedding** `e`, the half-order bound, host transitivity, `PublishedRecognitionSources`,
`OrthogonalSearchChecks`, `SmallPaleyExclusions`, `PrimitiveFiniteChecks`, and
`NamedTaylorFiniteChecks`. These inputs are *parameters*, not hidden proofs of the cited classifications or of the stated finite checks.

| Paper case | Lean alternative / audit | Limit of what has been certified |
|---|---|---|
| (1), homogeneous | `primitiveCases` and Gardiner input | Correct for every induced selection; Gardiner remains an accepted external theorem. |
| (2), triangular `T(n)` | `TriangularPair` tests the **actual selected edge set** of `K_n` | The paper's *abstract line graph of a triangle-free graph* wording needs the half-order bridge below; it is not definitionally identical to `TriangularPair`. |
| (3a), disjoint or Taylor double of homogeneous `G` | Canonical imprimitive/Taylor witnesses and `validation/ArbitrarySelectedCopies.md` | Both selected-embedding transport and the homogeneous-base restriction matter; do not replace `G` with an arbitrary nonhomogeneous graph. |
| (3b), generalized clique cover | `EqualCliqueHostModels` for the **selected** `sK_t` | The selected lower cliques and the outside upper cliques are part of the model, not just an abstract host isomorphism. |
| (3c), two unequal cliques joined by a matching | `twoCliqueMatchedGraph c true` and its `G`-fixed isomorphism | All abstract embeddings are covered by the documented matching-transversal symmetry. |
| (4a–f), Wagner/C₅/R₃ | `CycleFiveSmallHostPatterns`, `RookSmallHostPatterns`, Wagner canonical model | The corrected (4e) matching is compatible with rook adjacency in the opposite-complement orientation; the bare arbitrary-matching version is false. |
| (4g), icosahedron | `IsTaylorTransversalCopy icosahedralTaylorBase` | Independent enumeration: of 924 six-subsets, exactly 64 selected copies in the four stated abstract graph types pass the EPPA test (12+12+20+20). |
| (4h), rook `R₄` | `MatchesPrimitiveFigure` for two fixed large figures | Independent 16-bit orbit enumeration: 112 host-automorphism orbits of subsets of size at least 8; precisely 7 positive orbits, matching the abstract subgraph descriptions. |
| (4i), Clebsch | `MatchesPrimitiveFigure` and external `CanonicalFigureClassification` | Independent 16-bit orbit enumeration: 88 host-automorphism orbits of subsets of size at least 8; ten figure-induced **abstract graph types**, with no positive/abstract mismatch. The exhaustive EPPA classification is a specified finite input. |
| (4j), `J(6,3)` | `IsTaylorTransversalCopy johnsonTaylorBase` | All 184,756 ten-subsets were screened by their rooted two-graph descendants. Exactly 1,024 have descendant `R₃`; all are complementary-pair transversals. Thus the Petersen-switching wording agrees with the Lean transversal clause. |
| (4k), Schläfli | `MatchesPrimitiveFigure`, fourteen fixed maximal figure subsets, external finite check | The drawings-to-mask correspondence is checked in `validation/primitive/positive-figure-audit.md`. **The exact Lean conclusion is orbit-based**, whereas “is an induced subgraph of a displayed graph” can be read as an abstract-isomorphism condition. A complete abstract-copy-to-host-orbit equivalence has **not** been certified by this audit. |

### Triangular abstract-graph versus selected-edge-set bridge

Let (F\subseteq E(K_n)) represent the chosen vertices of (T(n)), (n\ge5), with
(|F|\ge n(n-1)/4), and suppose its line graph is isomorphic to that of a
triangle-free graph (Q) on (n) vertices. Whitney's line-graph exception
exchanges an isolated triangle component with a three-edge star component.
But if (Q) contained a three-edge star component, Mantel's bound on its
remaining (n-4) vertices would give
[
|E(Q)|\le 3+\lfloor (n-4)^2/4\rfloor < n(n-1)/4,
]
a contradiction. Hence the Whitney exception cannot occur, and the selected
edge set (F) is triangle-free. This is a **paper-level bridge**, not a Lean
lemma, and needs either citation or inclusion when treating case (2) as an
abstract line-graph statement.

### Outstanding source-to-formalization caveats

1. The printed theorem's `\leanpartialpinned` annotation still claims that (4e) needs the corresponding-vertex condition; **that comment is obsolete** in the uploaded 14:37 source and should be updated, without changing the theorem.
2. The Schläfli finite premise proves orbit-based sufficiency/necessity for the **actual embedding**. The complete implication from the manuscript's potentially broader abstract-isomorphism reading to this orbit predicate is a separate obligation. No contradiction has been found; it must not be silently marked Lean-verified.
3. The main theorem's Lean proof is **conditional** on externally published catalogue/recognition data and finite checks. The full paper proof and the exact data import are not certified simply by a successful kernel check.
4. The introductory imprimitive summary omits the optional mate matching and some exceptional homogeneous-base hosts. That is a prose-level issue, separate from the corrected case (4e) statement.

Do not claim an unconditional formalization of Gardiner, the rank-three group catalogue, or the separately specified computations. The exact checked statements and their hypotheses take precedence over comments in the manuscript.
