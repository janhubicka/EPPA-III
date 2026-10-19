# Direct lifting of two-graph automorphisms — 20 October 2026

**Frozen manuscript:** `main-new(20261019-085906).tex`, Section 5.1, `lem:2trans`.

The converse assertion that every automorphism of the associated two-graph lifts to an automorphism of its Taylor double can be proved directly, without invoking the Mallows–Sloane invariant-graph theorem.

Write `e(x,y)` for the F₂-valued adjacency indicator of any graph representative of the two-graph. Given `f ∈ Aut(Δ)`, put
\[
  \delta(x,y)=e(x,y)+e(fx,fy).
\]
Preservation of triple parity yields `δ(x,y)+δ(y,z)+δ(z,x)=0`. Fixing a base point `r` and setting `h(x)=δ(r,x)` gives
\[
  \delta(x,y)=h(x)+h(y).
\]
(For empty X, the statement is vacuous.) In the Taylor double, a pair of vertices from distinct fibres is an edge exactly when
\[
  e(x,y)+i+j=1\quad\text{in } \mathbb F_2.
\]
Thus the permutation
\[
  \widehat f(i,x)=(i+h(x),f(x))
\]
preserves every adjacency and nonadjacency and covers `f` under the natural projection. This explicitly supplies the missing reverse inclusion `Aut(Δ)⊆mathrm{im}(Aut(H)→Sym(X))` and requires **no coherent choices** of partial automorphism extensions.

The Lean modules `EPPAIII/TwoGraphs/XorSwitchingPotential.lean` and `EPPAIII/TwoGraphs/TaylorAutomorphismLift.lean` implement the construction and are under CI/axiom audit in this branch.

**Other inclusion:** PR #326 proves that a fibre-preserving host automorphism preserves triangles across three fibres, then identifies that intrinsic property with odd-edge-parity triples. Together the two PRs certify equality of the induced group and Aut(Δ), *conditional on the intrinsic fibre system*.

**Remaining upstream obligation:** derive fibre invariance from EPPA and non-homogeneity via the true-twin quotient argument in `lem:fibre-rigidity`. The graph-distance half of that lemma and induced 2-transitivity conditional on fibre invariance are already Lean-verified.

No changes to the author manuscript; this note is a proposal for future source validation markers and optional shorter exposition.
