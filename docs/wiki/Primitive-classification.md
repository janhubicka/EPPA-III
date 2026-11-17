# Primitive EPPA witness classification

## Statement to verify

Let `H` be a finite simple graph whose full automorphism group acts transitively on vertices. Fix a finite simple graph `G` and a particular induced embedding `e : G ↪ H`. Suppose `|V(H)| ≤ 2|V(G)|`. The classification in R17, `thmintro:classification`, asserts that `IsEPPAEmbedding G H e` is equivalent to the following list, with simultaneous complementation of both graphs permitted.

| Case | Host and selected graph |
|---|---|
| 1 | A homogeneous host, with any induced selection. Gardiner's list gives `C₅`, `R₃`, and equal-sized disjoint clique unions, together with their complements. |
| 2 | `T(n)` for `n ≥ 5`, with the selected graph the line graph of a triangle-free graph on `n` points. The Lean target formulates triangle-freeness for the selected edges in the given host embedding. The passage to abstract line-graph isomorphism is a separate step. |
| 3(a) | Exact doubled order, with a homogeneous selected graph and host its disjoint double or Taylor double. |
| 3(b) | Exact doubled order, with an equal-sized disjoint clique union and a generalised clique cover of it. |
| 3(c) | Exact doubled order, with two selected cliques of distinct sizes and the host two cliques of the total selected order joined by a perfect matching. |
| 4(a–f) | Wagner / `2K₂`. `C₅` prism / `C₅`. Complement of the 2-clique extension of `C₅` / `C₅`. `R₃` prism / `R₃`. Matched `R₃ ⊔ complement(R₃)` / `R₃`. Complement of the 2-clique extension of `R₃` / `R₃`. |
| 4(g–k) | Icosahedron / the four stated six-vertex forms. `R₄` / induced subgraph of `R₃ ⊔ K₁` or `L₄,₂`. Clebsch / induced subgraph of a listed figure model. `J(6,3)` / a Petersen switching mate. Schläfli / induced subgraph of a listed figure model. |

The table is a specification of the manuscript's target. In the final Lean disjunction each row needs a graph model, and rows whose necessity or sufficiency depends on the embeddings must retain `e` or prove that the abstract pair condition determines the required property. Figure models need exact adjacency data. The size condition remains in force when a maximal figure model is replaced by an induced subgraph.

## How the primitive proof connects

1. The exact small-host trichotomy gives a complete graph, an edgeless graph, or a rank-three full automorphism action. Its conditional primitivity hypothesis is needed at exact doubled order. The homogeneous and imprimitive cases are discharged separately.
2. In a rank-three host, an automorphism fixing a selected vertex preserves the neighbours and the distinct non-neighbours. Extending a partial map while fixing that vertex transports EPPA to the selected vertices in each part.
3. The two parts and the selected vertex partition the host. Cardinality forces a part with at least half of its vertices selected. Both parts are transitive and strictly smaller, allowing the minimal-counterexample argument to invoke the **pair** classification. Using the host alone discards information needed in the stabilizer argument.
4. The rank-three catalogue identifies the ambient graph. Subconstituent identifications, parameter screens, local action bounds, finite checks and family exclusions are separate obligations. Complementation interchanges the two parts.
5. The final theorem needs both the necessity argument and the positive witness constructions or exact positive finite checks. Neither the trichotomy nor the catalogue supplies that equivalence.

The rank-three assumptions and finite computation boundary are listed on the [assumptions page](Primitive-classification-assumptions).

## Verification status

The small-host trichotomy is available in the repository. The family exclusions and final primitive classification are in progress. The pages here document the proof obligations and the source for each input.

## Local checks

The repository pins Lean in `lean-toolchain` and mathlib in `lakefile.toml`. Run `lake build`, then:

```bash
lake env lean CheckAxioms.lean > axioms.log 2>&1
python3 scripts/check_axioms.py axioms.log CheckAxioms.lean
```

The axiom check detects proof dependencies introduced through Lean axioms. To audit explicit theorem parameters such as an external classifier, also inspect the theorem types. Progress on the primitive part is recorded in the validation directory.
