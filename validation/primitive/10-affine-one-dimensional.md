# EPPA III affine-line repair

This repair replaces the proof of R17 Lemma 8.26. The lemma names the sporadic Peisert graph explicitly because it is distinct from the ordinary Peisert graph of order 529.

## Incorrect stabilizer orders

| Host | Order of the full point stabilizer | Subdegrees | Order of the full pointwise pair stabilizer |
|---|---:|---:|---:|
| Peisert, 49 vertices | $3\lvert SL_2(3)\rvert=72$ | $24,24$ | $3$ |
| Peisert, 81 vertices | $4\lvert SL_2(5)\rvert=480$ | $40,40$ | $12$ |
| Ordinary Peisert, 529 vertices | $11\cdot3\lvert Q_8\rvert=264$ | $264,264$ | $1$ |
| Sporadic Peisert, 529 vertices | $11\lvert SL_2(3)\rvert=264$ | $264,264$ | $1$ |

The rank-three point stabilizer is transitive on each of the two off-diagonal root classes. Orbit–stabilizer therefore divides the first column of group orders by the corresponding subdegree. The group descriptions come from Brouwer and Van Maldeghem, *Strongly Regular Graphs*, preprint printed pages 267, 283 and 325, §§10.18, 10.30 and 10.70. The full groups are also identified in Guo, Vasil'ev and Wang, Proposition 3.1 and Tables 4–5. [Brouwer and Van Maldeghem](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf) · [Guo, Vasil'ev and Wang](https://arxiv.org/pdf/2406.04559)

R17 uses the Paley pair orders 2 and 4 in the two exceptional ordinary Peisert cases. The revised proof excludes 49 and 529 vertices by the uniform bound $4t+2$. At 81 vertices, a selection contains at least 41 vertices. After fixing two selected anchors, there is a profile class with at least ten selected vertices. It lies inside a single orbit of the order-12 stabilizer. The orbit length divides 12 and must be 12, so fixing any third selected point in that orbit leaves the identity. The existing three-anchor profile bound gives $2^3+3=11$, a contradiction.

## Uniform argument with the full group

For any two selected anchors, vertices with the same adjacency profile lie in one orbit of the full host pair stabilizer. This follows by extending a partial map on three vertices. A pair stabilizer of order at most $t$ therefore gives $|G|\le4t+2$.

For a host whose full group is contained in $A\Gamma L_1(q)$, a map fixing two distinct anchors is determined by its Galois component. Thus $t\le r$ for $q=p^r$ and $|G|\le4r+2$. The half-order condition imposes $p^r\le8r+4$. The elementary arithmetic leaves only Paley orders 5 and 9, Peisert order 9, and Van Lint–Schrijver pairs $(q,e)=(4,3),(16,3),(16,5)$. The first two Paley cases are the pentagon and $R_3$, and Peisert order 9 gives the same rook graph. The Van Lint–Schrijver pairs give a matching, the Clebsch graph, and four disjoint copies of $K_4$. The included checker explicitly relabels the order-16, index-3 connection set to the Clebsch generators $1,2,4,8,15$ and verifies all 120 unordered pairs.

The pair-stabilizer bound requires containment of the **full** automorphism group of the actual graph in $A\Gamma L_1(q)$. Brouwer and Van Maldeghem §7.4.4 gives the full Paley group. Guo, Vasil'ev and Wang, Lemma 2.7 gives the ordinary Peisert containment outside the named exception range, and their Proposition 3.1 lists isomorphism identities for the exceptional Van Lint–Schrijver rows. The replacement spells out those identities and retains the dependencies on the preceding rook, affine-polar and bilinear cases and on the positive Clebsch classification. The source's 4098 typographical error in Table 4 denotes 4096, as in the proof of Proposition 3.1. [Brouwer and Van Maldeghem](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf) · [Guo, Vasil'ev and Wang](https://arxiv.org/pdf/2406.04559)

## Apply and verify

- **R17-affine-one-dimensional.patch** applies directly to **main-new(20261116-151839)-markers-r17.tex**. Its replacement overlaps the Paley paragraph of W08 and supersedes that paragraph. The rank-two polar edits from W08 remain separate.
- **R17-affine-after-prior-cumulative.patch** is the equivalent increment for the previously assembled **primitive-followup-repairs/proposed.tex**, provided that file is named as the original manuscript. Use exactly one patch against the corresponding baseline.
- Both patches pass **git apply --check**. Applying the frozen-base patch reproduces the generated proposed file byte for byte.
- **latexdiff.tex** is the full-source LaTeX diff against frozen R17. **latexdiff.pdf** is its two changed pages, compiled through the usual review renderer.
- **python check-affine.py** verifies the numerical cutoffs, exceptional order divisions, the 81-vertex orbit divisibility, and the two order-16 graph identifications. It uses only the Python standard library. The cited full automorphism classifications remain external inputs.
