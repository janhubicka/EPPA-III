# A shorter fibre-rigidity contradiction by triangle counts — 20 October 2026

**Target:** Lemma `lem:fibre-rigidity` in the frozen `main-new(20261019-085906).tex`. This is an *optional author-facing alternative*, **not** an edit to the manuscript and **not yet a full Lean theorem**. It avoids the true-twin quotient / independent-set counting argument.

## Reduction already certified in Lean

Suppose a pair of base vertices lies in no even-parity triple. Its adjacent lifts in the Taylor double are true twins (merged PR #328). Given EPPA, the two-point maps carry this property to every selected edge, hence the selected graph G is a cluster graph (PR #329, integration CI pending). We must show that **if G is a cluster graph, its Taylor double is vertex-transitive, and Δ(G) is nontrivial, then G is homogeneous.**

## Triangle-count proof

Write the connected components of the cluster graph as `C_1,...,C_s`, with positive sizes `t_i=|C_i|`; let `n=sum_i t_i`. If `s<=2`, every triple of G spans either one or three edges. Thus Δ(G) is complete, contradicting nontriviality. Hence `s>=3`.

For three distinct base vertices, a triple is **outside Δ(G)** precisely when its members lie in *three different* components. Over such a triple, the Taylor double induces a 6-cycle; over an odd triple, it induces two disjoint triangles. A fixed lift of a base point `x∈C_i` lies in precisely one host triangle for each odd triple containing x. Consequently the number `T_i` of triangles through this lift is

[
  T_i=inom{n-1}{2}
      -sum_{substack{j<k\\j,k
e i}}t_jt_k.
]

Since the Taylor double is vertex-transitive, these triangle counts are independent of i. For any distinct i,j, subtracting gives

[
 T_i-T_j=(t_i-t_j)sum_{k
e i,j}t_k.
]

The final sum is strictly positive, because s≥3 and each component is nonempty. Thus `t_i=t_j` for all i,j. We conclude `G≅sK_t`, a homogeneous graph, contradiction.

This finishes the key implication of Lemma `lem:fibre-rigidity` once the two preceding Lean statements are combined. It requires no graph classification, quotient construction, coherent EPPA lifts, or outside references.

**Independent finite audit:** I directly counted the triangles through each lift in every Taylor double corresponding to an integer partition of n for n=3,...,10. The formula passed for 1,101 base-vertex positions. This test corroborates the symbolic formula, but arbitrary-size proof is the elementary double counting above.

## Verification boundary

- The two-point true-twin and EPPA-to-cluster steps are now formally checked in PRs #328 and #329 (check #329 CI/merge before marking the composition green).
- The triangle-count formula and the component-size conclusion are proved on paper here, **not yet formalized in Lean**.
- The remaining source choice is whether to retain the existing true-twin quotient proof or replace it with this shorter count. Both avoid the external Gardiner/rank-three classifications.
- Do not modify the frozen manuscript or circulate the correction to Sofia before the deferred author review.
