# Localized source rationale: R3 Claims 6.15–6.16

**Source:** reorganized `main-new(20261016-172438).tex`. This directory contains **suggestions only**; the author's manuscript remains unchanged.

- **Claim 6.15:** the source proof already has the correct structure. The displayed replacement merely states the orbit obstruction more directly. Certified by `rook_eppa_nontrivial_imprimitive_block_sizes` in PR #286, green Lean CI. Mark only the claim itself green, not every original sentence.
- **Claim 6.16, 9-vertex blocks:** the generalized filled-half transport in PR #288 and its R3 specialization in PR #289 are green. Unlike separated-component proofs, these allow arbitrary edges between the two host blocks.
- **Claim 6.16, 2-vertex blocks:** the pair-invariant outside-graph theorem PR #287 and its actual-block application PR #290 are green. They use real EPPA lifts of the 72 rook permutations, not a postulated coherent action.
- **Self-complementarity:** PR #291 formalizes the explicit index map `(x,y) → (x+y,x−y)` over `Fin 3`. The combined original-host conclusion is PR #293 and must pass CI before upgrading Claim 6.16 to a green marker.
- **Remaining Lemma 6.14:** deduction of a common cross degree from host transitivity and equal 4-regular halves (PR #292); reduction of degrees 5–9 by graph complementation and reindexing; exact identification of the remaining canonical finite graphs (conditional k≤4 theorem PR #285 is green). Do **not** mark the full lemma green before these bridges are checked.

No theorem of Gardiner, rank-three graph classification, or unverified outside action is used here.
