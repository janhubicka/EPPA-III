# EPPA III: Section 8 factorial bound and halved-orthogonal q=2 audit (4 November 2026)

**Scope:** frozen manuscript `main-new(20261031-234151).tex`. This is a **paper-level validation and proposed repair**, **not a Lean proof**. No author prose or existing TODO is modified by this PR.

## 1. Perfect generalized clique covers

Every generalized clique cover in Definition `def:generalizedcover` is perfect, as is its complement. Indeed, its vertex set is partitioned into two sides `C_1,...,C_s` and `D_1,...,D_s`, each a disjoint union of cliques. Between `C_i` and `D_j` for `i != j`, adjacency is uniform (empty or complete).

An induced chordless cycle of length at least five cannot contain consecutive vertices `u,v` from one cell `C_i`: their predecessor and successor would both have to be in `D_i` (otherwise an off-diagonal edge hits both `u,v`, giving a chord), yet `D_i` is a clique, a contradiction. The same holds for every `D_i`. Hence every induced long cycle alternates sides, so is even.

If there were an induced odd antihole on `2j+1 >= 7` vertices, at least `j+1 >= 4` vertices would lie in the same side. Their complement induces a complete multipartite graph in `C_(2j+1)`. A complete multipartite induced subgraph of a cycle on at least four vertices is independent (else it contains a triangle, degree-three vertex or 4-cycle), contradicting `alpha(C_(2j+1)) = j`. The five-vertex antihole is a five-cycle, excluded above. By the Strong Perfect Graph Theorem (Chudnovsky, Robertson, Seymour, Thomas, *Annals of Mathematics* 164 (2006), 51–229, DOI 10.4007/annals.2006.164.51), the cover and its complement are perfect.

Thus any induced `F` in such a graph satisfies `|F| <= alpha(F) * omega(F)`. In particular, for **the actual selected** `G_alpha` with `|G_alpha| >= |H_alpha|/2` under `ass:classification`, there is a clique/independent set of size at least `r = floor(sqrt(|H_alpha|/2))`. By `cor:local-section`, its symmetric group `S_r` is a **section of the original vertex stabilizer** `Aut(H)_v`. This repairs the numerical factorial bound without assuming that `G_alpha` is the canonical equal-clique half. The false stronger `sqrt(|H_alpha|)` bound for homogeneous hosts is *not* claimed.

**Formalization boundary:** SPGT is an external theorem, not Lean-certified in this project. A direct Lean proof of `alpha(F) * omega(F) >= |F|` for this graph class is a natural next goal. A particular downstream use involving `H_2` still requires establishing `|G_2| >= |H_2|/2`; it cannot be inferred solely from the fact that `H_2` is a generalized clique cover.

## 2. Halved orthogonal q=2: direct degree obstruction

The two subconstituents of `Delta_(1/2)(O^+_10(2))` have `(order, degree) = (310,85)` and `(1984,275)`. For a homogeneous equal-clique union or complement on `N` vertices, degree is `t-1` or `N-t`, `t|N`, and neither pair fits. A generalized cover on `N=2st` vertices has degree in

`{ t-1, t, 2t-2, 2t-1, st-1, st, st+t-2, st+t-1 }`.

Complementing changes `d` to `N-1-d`. For `st=155` (`N=310`), no divisor `t|155` gives `d=85` or `224`; for `st=992` (`N=1984`), none gives `d=275` or `1708`. **Both** constituents are thus excluded, independently of the old unjustified `S_31` argument. Excluding only `H_1` would be insufficient because `ass:classification` merely provides some suitable `alpha`.

## 3. Local-section citations

The `M_22` and Higman–Sims explicit independent sets yield their sections in `Aut(H)_v` by `cor:local-section`, not the factorial remark. In the generic Paley/Peisert argument, lack of an `S_4` section in `Aut(H)_v` implies that **neither selected subconstituent** `G_1,G_2` contains a 4-vertex clique or coclique; it does not exclude 4-vertex cliques/cocliques from all of `G`. This correctly gives `|G_i| <= 17` by `R(4)=18`.

## Audit and policy

The two repairs above and the cross-reference corrections passed paper-level adversarial review; finite tests of small covers (including odd hole/antihole screens and `alpha*omega` checks) and all 16 cover/complement degree possibilities for the `q=2` case passed. **No new Lean theorem or CI certification is asserted.** Prior commented-out or withdrawn manuscript notes are not reintroduced. The larger binary-orthogonal `lem:o2` and exceptional `E_(6,1)(q)` gaps remain separate.
