# Final imprimitive proposition — equal-clique interface

**Manuscript:** current Proposition 6.17, equal-clique paragraph; the author TeX is unchanged.

The printed Lemma 6.1 assumes the complementary induced half is already sK_t. Its invocation in Proposition 6.17 does not discharge this hypothesis, which is a real logical gap in the paper-level argument.

**Corrected theorem (pending CI):** `EPPAIII.CliqueCovers.eppa_noncluster_clique_double_all_positive` classifies an arbitrary vertex-transitive *non-cluster* double-sized EPPA host H of G=sK_t for s,t≥1 without any outside-half assumption. The conclusion constructs a graph equivalence fixing the selected copy and identifies H with a generalized clique cover or the 2K2 Wagner exception. No imprimitive host partition is assumed.

The proof combines the already certified stronger s,t≥2 profile orbit theorem, s=1 complementary independent-set construction, and the t=1 edge-count/outside-independent result. The only source-facing bridge still needed for the proposition is elementary: a finite vertex-transitive disjoint union of cliques has equal component sizes and is homogeneous. Thus a **non-homogeneous** vertex-transitive H cannot be a cluster graph.

**Minimal source repair:** the direct self-contained profile proof supplied in `validation/lemma6-1-proposed-proof.tex` should replace the printed Claims 6.2–6.5 before Proposition 6.17 cites the stronger form. Alternatively, state and prove a separate non-cluster corollary. Do not cite the present restricted Lemma 6.1 without addressing its outside-half hypothesis. The complement-of-clique-union case is handled by complementing G and H together, not by applying Lemma 5.12 (which explicitly excludes it).

The manuscript's Wagner alternative should not say “or its complement” after the displayed 3-regular Wagner matrix: its complement is 4-regular.

**Validation status:** all constituent proof theorems passed Lean CI on the GCC PR chain (#278–#279); this new interface awaits its own CI and axiom audit.
