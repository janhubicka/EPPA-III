# EPPA-III validation changelog — 16 October 2026

**Reference:** latest main-new(3).pdf, with independently applicable patches prepared against main-new(8).tex. The author manuscript stays **unchanged**. Former Section 3 is now §§5.3 and 6; the exact cross-reference map is in section5-6-source-map.tex.

## Lean checkpoint
ImprimitiveClassification.lean assembles verified building blocks into the actual-host double-cover conclusion of Lemma 5.12. It constructs the second-half coordinates and gives Taylor adjacency with uniformly optional mate edges, plus ordered inter-block edge/nonedge transitivity. Non-homogeneity of G is explicit; the Gardiner-classification bridge and exact original-proof wording remain separate. Check green CI and permitted axioms before certification.

## Most localized patch proposals
- **P01 — Claim 5.15 (Lean-backed):** Restrict the strict Taylor adjacency assertion to edges between different blocks. Within each block, vertex-transitivity permits a uniform matching of mates.
- **P02 — Claim 6.3 (Lean-backed orbit):** A lift can move D_j. Count the full orbit of an outside neighbourhood profile, at least s·binom(t,k) among st outside vertices, rather than subsets seen in one D_j.
- **P03 — Claim 6.4 (partial):** Count the Sym(s)-orbit of coloured subsets among s D-cliques. This repairs the numerical statement but **not** the unproved simultaneous matching-coordinate normalization.
- **P04 — Lemma 6.6 (necessary):** Require non-homogeneous H. Homogeneous EPPA witnesses such as K₂ ⊔ K₁ inside 3K₂ and K₃ ⊔ K₂ ⊔ K₁ inside 4K₃ contradict the unqualified statement.
- **P05 — Lemma 6.12 (Lean-backed):** C₅'s two orbits of pairs each have size five. EPPA invariance of actual outside neighbourhoods rules out a C₄ ⊔ C₆ cross incidence; primality alone does not.
- **P06 — Lemma 6.14 (Lean-backed):** R₃ has 2-subset orbit sizes 18,18 and 3-subset orbit sizes 6,6,36,36. No invariant multiset of nine outside profiles has either size.
- **P07 — Lemma 6.1 (Lean/finite checks):** The claim itself must permit ordinary-cover alternatives: transitivity alone does not identify Wagner, since the cube is transitive but fails EPPA. Also repair the missing set brace and the false assertion that Wagner is isomorphic to its graph complement.
- **P08 — Proposition 6.17 (assembly still open):** Include non-homogeneous doubles 2C₅, 2R₃ and 2G; handle complements of clique unions by complementing G and H together, rather than misapplying Lemma 5.12.
- **P09 — Definition 1.6 discussion (immediate):** The Taylor double of K_t is 2K_t (X=0); X=M adds the perfect mate matching.

## Do not silently close
The original proofs of Claims 6.2 and 6.4 have further nonlocal gaps (regularity and simultaneous matching normalization). The alternative verified Lean classification avoids them; cosmetic changes do not certify those proofs. Proposition 6.17, exact exceptional host identifications, and the Gardiner bridge remain certification targets.

Individual patch files have passed GNU patch --dry-run -p1 against the uploaded main-new(8).tex. All editorial changes remain proposals.
