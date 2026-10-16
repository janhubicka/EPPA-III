# R3 low-cross-degree classification (current Lemma 6.14)

Theorems in the `RookThreeZeroCrossConclusion.lean` and `RookThreeSmallCrossConclusion.lean` modules consolidate independently validated EPPA classifications. The latter is **conditional** on every outside vertex having the same cross-degree `k ≤ 4`.

The classification is exact: at k=0, H=2R3; at k=1, H is one of two explicit canonical matching models; at k=2 or 3 no such EPPA host exists, by invariant neighbourhood-profile multiplicities; at k=4, H is one of two canonical rook doubles. All graph equivalences preserve the designated embedded R3.

**Open steps before claiming the entire Lemma 6.14:** (1) prove the block-size-2/9 dichotomy from primitivity of the rook action; (2) derive outside graph ≅ R3 without pre-labelled outside action; (3) deduce uniform outside cross-degree and the complement reduction from the two-half structure; (4) identify the canonical models with the exact paper graph names, accounting for the self-complementing permutation of R3.

This does not prove the manuscript statement in isolation; green markers should be attached to each conditional case theorem only. Original TeX remains unchanged.
