# A shorter fibre-rigidity contradiction by triangle counts — 20 October 2026

**Target:** Lemma `lem:fibre-rigidity` in the frozen `main-new(20261019-085906).tex`. This is an *optional author-facing alternative*, **not** an edit to the manuscript and **not yet a full Lean theorem**. It avoids the true-twin quotient / independent-set counting argument.

## Reduction already certified in Lean

Suppose a base pair lies in no even-parity triple. Its *adjacent lifts* in the Taylor double are true twins (merged PR #328), but **they may lie on opposite sides of the natural transversal**. The EPPA propagation theorem in PR #329 applies only if a true-twin class contains an actual selected edge (two vertices of G). This is the **first case** of the manuscript's quotient argument, not its entire proof. In that case EPPA proves G is a cluster graph, and the following triangle-count argument proves that a vertex-transitive Taylor double with nontrivial Δ cannot have unequal component sizes. The **second case**, where every true-twin class meets G in at most one vertex, still needs the original quotient/transversal reasoning.

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

This gives a short, quotient-free contradiction **only in the first case**, when some selected edge has true-twin endpoints. It does **not** replace the second case of the source proof. It requires no external classification or coherent EPPA lifts.

**Independent finite audit:** I directly counted the triangles through each lift in every Taylor double corresponding to an integer partition of n for n=3,...,10. The formula passed for 1,101 base-vertex positions. This test corroborates the symbolic formula, but arbitrary-size proof is the elementary double counting above.

## Verification boundary

- The true-twin calculation is formalized in PR #328; the conditional **selected-edge** propagation theorem is in PR #329 (check its CI/merge before marking it green). Neither theorem asserts that every bad base pair gives a true-twin edge inside the selected transversal.
- The triangle-count formula and the component-size conclusion for the cluster case are proved on paper here, **not yet formalized in Lean**. The original proof's second case (one selected vertex per true-twin class) remains necessary.
- The remaining editorial choice is whether to shorten the **first branch** of the true-twin quotient proof using this count, while retaining the second branch. Both routes avoid the external Gardiner/rank-three classifications.
- Do not modify the frozen manuscript or circulate the correction to Sofia before the deferred author review.
