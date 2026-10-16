# Lemma 6.1: self-contained generalised clique-cover audit (16 October 2026)

**Source:** main-new(20261016-172438).tex, Lemma 6.1, Claims 6.2–6.5. The author's manuscript is unchanged. External Gardiner and rank-three classifications are not used.

## Lean-certified core

For s,t >= 2, non-cluster vertex-transitive EPPA hosts H of order 2st containing the designated G = sK_t are completely classified: either H is a uniform generalized clique cover, or s=t=2 and H is the Wagner graph. The theorem **does not assume** H is imprimitive or H\G = sK_t. The fixed-base variant proves that the coordinate equivalence preserves the specified embedding of G. The old theorem names remain available.

## Combinatorial proof (the main fragile steps)

Let B=H\G. Vertex transitivity and equal half sizes give |E(H[B])| = |E(G)| = s*binom(t,2). For each outside w, define its neighbourhood profile P(w) by the s selected cliques. Every element of S_t wr S_s extends by EPPA; the entire orbit of P(w) occurs among the st outside vertices, so its size is at most st. No coherent choice of lifts is needed.

Call a coordinate partial if its size is strictly between 0 and t; let p be the number of partial coordinates. For 2 <= p < s the orbit has at least binom(s,p)*t^p > st elements. For p=s>=2, t^s>st except s=t=2. Hence there is at most one partial coordinate outside the exceptional case.

If p=1, with partial size k and r additional full coordinates, the orbit has exactly s*binom(t,k)*binom(s-1,r) profiles. The bound <= st forces k=1 or t-1 and r=0 or s-1. This orbit has exactly st members and exhausts B. The induced action on B is the natural S_t wr S_s action on s blocks of t points; unordered pairs have two orbits (same/different block). The half-edge equality forces H[B]=sK_t. The cross-relations are diagonal matchings/co-matchings with uniformly empty/complete off-diagonal entries.

If p=s=t=2, the four outside profiles form the corners of a square; unordered-pair orbits have sizes four and two. The outside half has exactly two edges, so it is the opposite-corner matching; the entire host is the Wagner graph.

If p=0 for every outside vertex, each selected C_i lies in one true-twin class of H. In the non-cluster transitive host all twin classes have a common size a>=t, and the twin quotient has M=2st/a<=2s vertices. The selected s classes form an independent set. Since the quotient has positive regular degree, s<=M/2, forcing a=t and M=2s. The complementary s twin classes comprise B, and half-edge equality prevents edges between them. Their cross-neighbourhoods are unions of full selected cliques, encoded by s masks R_j subset [s] of one size r. EPPA makes the family invariant under S_s, hence binom(s,r)<=s. Therefore r is 0,1,s-1,s, giving precisely the uniform diagonal/off-diagonal forms.

These direct cases avoid the unsupported original irregular-block counting of Claim 6.2, the simultaneous matching-normalization in Claim 6.4, and the varying-independent-transversal degree claim of Claim 6.5. They establish the conclusion independently rather than certify the original prose.

## Remaining source hypothesis: cluster H

If H is a disjoint union of cliques **and H\G=sK_t** as required by the printed lemma, each host component contains at most one selected C_i and one outside D_j. Thus its order is t or 2t. Vertex transitivity forces a uniform size: H=2sK_t or H=sK_(2t). Both are generalised clique covers (X=0,Y=0 or X=1,Y=0 after reindexing). This short case is checked on paper but is not yet packaged into a Lean theorem.

The extra half-partition assumption is essential in the cluster case. Counterexample: H=4K3 is a homogeneous (hence EPPA) host containing G=3K2 by choosing two points in three different components. H has twice the order of G, but H\G = K3 plus three isolated vertices, not 3K2. All 1,999 partial automorphisms of this G were independently checked to extend through the component permutation action.

## Low parameters s=1 or t=1

At s=1, half-edge equality gives H[B]=K_t, and a profile of size k has orbit binom(t,k)<=t, so k in {0,1,t-1,t}. A size 1 or t-1 profile saturates B and gives a (co)matching; otherwise profiles are empty/full and regularity prohibits a mixture. At t=1, both halves are independent and the analogous S_s orbit argument yields empty, complete, matching or co-matching cross-relations. These cases are paper-audited; the outside-half equal-edge statements, but not the complete low-parameter normal forms, are already in Lean.

## Source-facing corrections and priorities

1. In Lemma 6.1(2) delete 'or its complement' after 'Wagner graph'. The displayed matrix has degree three; the complement is degree four. Treat complements by complementing both G and H, not by claiming the displayed matrix gives both.
2. Prefer a single compact direct profile proof in place of Claims 6.2–6.5; do not mark those claims individually Lean-verified merely because the replacement proves the same conclusion.
3. Finish the cluster-host and low-parameter cases in Lean, then export a theorem with the exact Lemma 6.1 hypotheses.
4. For the non-homogeneous host used in Proposition 6.17, H cannot be a cluster graph. Thus for s,t>=2 the strong Lean theorem removes the need to establish H\G=sK_t before applying the generalised cover classification. The exceptional degenerate parameters still need their own formalization.

**Formal validation:** commit 77ad68c09901507d3f4f9a8090f98834528acf64 passed GitHub Actions Lean build and axiom check. See the new fixed-base declarations in the three modified CliqueCovers modules. This note does not claim the cluster or degenerate cases are formally verified.