# Fibre rigidity and 2-transitivity audit — 19 October 2026

**Source:** `main-new(20261019-085906).tex`, `lem:fibre-rigidity` and `lem:2trans`. Source is frozen; this is validation only.

## Fibre rigidity: exact logical structure

The printed proof separates into two logically distinct facts.

1. Under non-homogeneity of the selected graph, a nontrivial two-graph, and EPPA of its Taylor double, **every distinct base pair belongs to a triple of even graph-edge parity** (a triple outside Δ). The proof is a true-twin quotient contradiction.
2. **Conditional on that pair-coverage property**, every mate pair in the Taylor double has graph distance exactly three, and every two vertices from different fibres have distance one or two. Thus the fibre partition is intrinsic and preserved by all graph automorphisms.

For (1), if all triples through a pair have odd parity, choose adjacent lifts; they are true twins. Vertex-transitivity of H forces uniform true-twin class size t≥2. The deck involution pairs the classes with no fixed class; write the quotient as Q on 2m vertices and |X|=mt. Regularity of H gives Q degree m−1. If m=1, H=2K_t and the two-graph is trivial. For m>1, either (i) some true-twin class contains two selected vertices, then EPPA makes *every* edge of the selected G internal to a true-twin class, so the occupied quotient classes form an independent set I; counting Q edges gives |I|≤m, while mt=|G|≤t|I|, forcing G=mK_t, homogeneous; or (ii) all selected intersections have size at most one, giving mt≤2m and t=2 with one selected vertex in each quotient class, so G≅Q; EPPA extensions descend to Q, making G homogeneous. Both contradict the hypotheses. This proof has been audited at paper level; the true-twin quotient argument is **not yet a complete Lean theorem**.

For (2), define the Taylor adjacency on Bool×X by:
\[
(b,x)\sim(c,y) \iff x\ne y\ \text{and}\ 
        \bigl((x\sim_G y)\iff(b=c)\bigr).
\]
Mates (b,x) and (!b,x) are nonadjacent and cannot share a neighbour, hence have no paths of lengths 1 or 2. A base triple of even parity produces a 6-cycle on its six lifts, giving a path of length 3 between mates. In the same 6-cycle, any distinct-fibre pair is either adjacent or has a common neighbour. This proves precisely the graph-distance characterization.

The new Lean file `EPPAIII/TwoGraphs/TaylorFibresDistance.lean` isolates the nonadjacency/common-neighbour and 2-/3-step constructions, **without assuming EPPA**. Together these certify the geometric half of the source argument once CI is green. The separate checker `checks/section5_taylor_fibre_distance.py` exhausts all switching classes with pair coverage through seven base vertices (263,032 rooted distance screens at n=7, all PASS).

## Lemma 2-trans: subsequent step

Once fibre rigidity is known, the induced permutation of base vertices preserves the two-graph (a triple induces two triangles or C6 according to its parity), and the Mallows–Sloane lifting argument (or the direct partial switching lemma with full domain) gives surjectivity onto Aut(Δ). EPPA is transitive separately on ordered base edges and nonedges. If these remained separate orbits under the induced group, all its permutations would preserve the selected G, making G homogeneous by descending every EPPA extension; contradiction. Therefore they are a single orbit and Aut(Δ) is 2-transitive.

This is a valid short paper argument; the complete induced-group theorem is not yet exported by Lean. Prioritize certifying (1) and the precise projection/isomorphism interface before marking `lem:2trans` green.

**Suggested source policy:** keep original proof prose unchanged; after verified code is merged, add a validation marker for the *conditional geometry theorem only* and retain a TODO on the EPPA/true-twin quotient reduction.
