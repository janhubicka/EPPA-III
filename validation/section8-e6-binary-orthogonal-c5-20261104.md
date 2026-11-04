# EPPA III — continuation: exceptional E₆ and binary orthogonal cases

**Date:** 4 November 2026.  **Frozen manuscript:** `main-new(20261031-234151).tex`, labels `lemma:e61q` and `lem:o2`. **Lean base:** `janhubicka/EPPA-III`, main `ee821458a28c881fb1e4acbb0216cc545729d20f`. This note gives **paper-level repairs and finite certificates, not new Lean theorems**. The two independent manuscript proposals are stored as localized unified patches; the author source remains unchanged in GitHub.

## 1. Elementary connected degree obstruction

A uniform generalized clique cover has vertex set `Bool × Fin s × Fin t`, order `N=2st`, and degree

\[
 d=t-1+c+(s-1)tY,\quad c\in\{0,1,t-1,t\},\quad Y\in\{0,1\}.
\]

If `s≥2` and `Y=0`, the cover is disconnected (distinct paired clique indices have no edges between them). Otherwise a connected cover on `N≥4` vertices has `d≥st−1≥N/4`. For a *complement* with `s≥2`, its degree is at least `(s−1)t≥N/4` (regardless of `Y`); with `s=1`, its only degrees below `N/4` are 0 and 1, giving respectively an empty graph or a disjoint matching, disconnected when `N≥4`. Hence

> **Every connected generalized clique cover or its complement, on at least four vertices, has degree at least one quarter of its order.**

The same inequality holds for connected disjoint unions of equally sized cliques and their complements. No EPPA, primitivity, or group-theoretic assumption enters this result.

## 2. Exceptional `E_{6,1}(q)` — complete conditional repair

Use the manuscript's external identification: the first subconstituent of the E₆ collinearity graph is a `q`-clique extension of the rank-three graph `D_{5,5}(q)`. The latter has order

\[
 n=(q+1)(q^2+1)(q^3+1)(q^4+1)
\]

and degree `d=q(q²+1)(q⁵−1)/(q−1)` (Ihringer's D₅,₅ graph paper, citing Brouwer–Van Maldeghem, *Strongly Regular Graphs*, Theorem 2.2.20). It is connected because its nonadjacent common-neighbour count is `(q²+1)(q²+q+1)>0`.

Thus the first constituent has `N₁=qn=k` vertices and degree `d₁=qd+q−1`. Direct factorization gives

\[
 N_1-4d_1=(q+1)(q^2-q+1)(q^3+q^2+q-1)(q^5-2q^2-q-4)>0\quad(q\ge2).
\]

The last factor is positive since `q⁵≥8q²` and `6q²−q−4>0` for `q≥2`. The first constituent is connected, regular, and has degree below `N₁/4`.

Using the parent graph's displayed `v,k` and the strongly regular parameter identity, the second constituent has

\[
 N_2=v-k-1=q^8(q^4+1)(q^4+q^3+q^2+q+1),
\]

and degree `d₂=k−μ<k`, where

\[
 \mu=(q+1)^2(q^2+1)(q^2-q+1)>0.
\]

For `q≥2`, `(q+1)²≤4q²`, `q²+1≤2q²`, `q²−q+1≤q²`, so

\[
 4k=4q(q+1)^2(q^2+1)(q^4+1)(q^2-q+1)
 \le 32q^7(q^4+1)<N_2.
\]

The strict inequality uses `q(q⁴+q³+q²+q+1)≥62>32`. The second constituent is connected by the **external** Brouwer–Van Maldeghem Proposition 1.1.12 already cited in the manuscript. Therefore it too has `d₂<N₂/4`. Both constituents fail every alternative of Hypothesis `ass:classification` — homogeneous equal-clique union/complement or generalized cover/complement. This repairs all prime powers `q≥2` without invoking the incorrect SRG-cover lemma on a clique extension.

Sanity checks: at `q=2`, the E₆ graph has `(v,k,λ,μ)=(139503,4590,621,135)`, with constituents `(N,d)=(4590,621),(134912,4455)`. At `q=3`, the constituent pairs are `(275520,10892),(65098242,274400)`.

**Proof boundary:** the algebra and degree obstruction are now checked; the local identification and second-constituent connectedness are external cited geometric facts, not formalized here.

## 3. Binary orthogonal graphs — a replacement for the diameter-three argument

The key *direct* obstruction is stronger and simpler than invoking perfectness: **all generalized clique covers are induced-`C₅`-free**. Suppose an induced five-cycle contains adjacent vertices in the same clique `Cᵢ` of the first half. Their predecessor and successor on the cycle cannot lie elsewhere in that half or in any `Dⱼ` with `j≠i` (off-diagonal adjacency to the two clique vertices is uniform). Therefore both lie in the clique `Dᵢ`, giving a chord. Similarly for the other half. Without any edge inside a clique, the cycle alternates between the two halves and hence has even length. Contradiction. Complements of covers are also induced-`C₅`-free because `C₅` is self-complementary. Unions of equal cliques and their complements are induced-`C₅`-free too.

The small base graphs below **all contain an induced `C₅`**. To make the finite check reproducible, encode `(x₀,…,xₙ₋₁)∈F₂ⁿ` by integer `Σ₂ⁱ xᵢ`. For plus type on six coordinates take `Q₊=x₀x₃+x₁x₄+x₂x₅`, and for minus type take `Q₋=x₀x₂+x₁x₃+x₄+x₅+x₄x₅`. The graphs `O₆^±` and `NO₆^±` take respectively nonzero singular and nonsingular vectors, adjacent iff their polar form is zero; `VO₆^±` takes all vectors, adjacent when the *distinct* pair has `Q(x+y)=0`. `Sp₄(2)` takes nonzero vectors in four coordinates with `b(x,y)=x₀y₂+x₁y₃+x₂y₀+x₃y₁`. Entries in each row below are in cyclic order:

| Graph | Five vertices inducing an exact `C₅` | `(v,k,λ,μ)` |
|---|---|---|
| `Sp₄(2)` | `1,2,4,12,11` | `(15,6,1,3)` |
| `O₆⁺(2)` | `1,2,8,24,55` | `(35,18,9,9)` |
| `O₆⁻(2)` | `1,2,4,12,27` | `(27,10,1,5)` |
| `NO₆⁺(2)` | `9,11,19,37,52` | `(28,15,6,10)` |
| `NO₆⁻(2)` | `5,7,11,17,24` | `(36,15,6,6)` |
| `VO₆⁺(2)` | `0,1,9,18,47` | `(64,35,18,20)` |
| `VO₆⁻(2)` | `0,1,5,10,23` | `(64,27,10,12)` |

The standalone regression enumerates all 10 pairs in each five-tuple, verifies the vertex predicates and adjacency, and independently reproduces the displayed strongly-regular parameters for all seven models. (Equal parameters alone would not identify an arbitrary SRG with its standard orthogonal model; here the models are *explicitly defined by the relevant quadratic forms*.)

The general extension step is straightforward from Witt decomposition: the standard six-dimensional plus/minus form is an orthogonal summand of every higher-dimensional nondegenerate form of the same sign, obtained by adding hyperbolic planes. Similarly the four-dimensional symplectic form embeds as an orthogonal symplectic summand. The induced five-cycles persist under these embeddings. Both a 2-clique extension and a Taylor extension contain a distinguished induced copy of their base graph (for the latter, the copy is inside the bottom layer).

Apply the manuscript's *external* constituent identifications (equations `eq:o2`, `eq:vo2`, `eq:vo2odd`, `eq:no2`):

| Parent family, outside the already treated small cases | Constituent 1 contains | Constituent 2 contains |
|---|---|---|
| Odd `O_m(2)`, `m≥7` | `O_{m−2}(2)`, hence `Sp₄(2)` | Same inside Taylor extension |
| Even `O_{2m}^ε(2)`, `m≥4` | `O₆^ε(2)` inside 2-clique extension | `VO₆^ε(2)` |
| `VO_{2m}^ε(2)`, `m≥4` | `O₆^ε(2)` | `NO₆^ε(2)` |
| `NO_{2m}^ε(2)`, `m≥4` | Odd orthogonal graph containing `Sp₄(2)` | `O₆^{−ε}(2)` inside Taylor extension |

Hence **both** constituents in every large case have an induced `C₅` and cannot lie in any of the four permitted classes under `ass:classification`. Together with the previously certified *small-order* cases, this closes the mathematical argument of `lem:o2`. It avoids both the invalid assertion that diameter three excludes covers and any appeal to the Strong Perfect Graph Theorem.

**Proof boundary:** the finite certificates and their preservation under standard coordinate embeddings have been audited. The source's constituent decomposition formulas and prior small-case EPPA exclusions remain external/paper/computational dependencies; this is not a fully Lean-formalized theorem. Do not upgrade the old small-case certificates to Lean-verified status.

## 4. Adversarial checks, output policy and outstanding tasks

- `python3 EPPAIII-20261104-exceptional-orthogonal-regressions.py` (or `python3 checks/section8_exceptional_c5_e6.py` in the validation repository) passes: 320 cover/complement model tests (connectivity, degree, induced `C₅`), all seven full six-dimensional SRG parameter sets and five-cycle certificates, and 50 exact E₆ parameter/inequality checks for `2≤q≤51`. The infinite-family conclusions rest on the written proofs, not extrapolation from these samples.
- Both targeted TeX patch variants pass `patch --dry-run -p1`; their contents compile in a 2-page LaTeX smoke test. Neither variant changes any prior author TODO, old/commented notes, statement, validation marker or theorem label. Only the prose of two previously identified faulty proofs is proposed for repair.
- The first patch targets the untouched `main-new(20261031-234151).tex`. The second targets `main-new(20261031-234151)-Nov2-plus-Nov4-proposed.tex`, *after* the earlier two days' independent repairs have been applied. Do not mix the two baselines.
- Formalization remains open: the no-induced-`C₅` lemma for arbitrary generalized covers is a valuable small standalone Lean target; the standard finite base certificates can be formalized via `decide`, and the geometric embedding/reduction remains an additional theorem dependency.
- Other sections still need audits for unjustified claims, missing assumptions and applications of the factorial-bound remark to a constituent for which the selected-half lower bound is not established. No closed or commented-out Sofia notes have been reintroduced.