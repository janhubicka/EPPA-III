# Primitive classification checkpoint

[`primitiveCases_iff_eppa_of_publishedRankThreeCoverage`](../../EPPAIII/Primitive/PublishedRankThreeCoverage.lean)
proves both directions of the primitive classification for the actual selected
embedding. The Lean build, axiom audit, finite checks and placeholder scan
passed at `946ec06`. [Integrated CI](https://github.com/janhubicka/EPPA-III/actions/runs/44106831662)

| Track | Checked result | Inputs to the proof |
| --- | --- | --- |
| Triangular and rook | Half-order criteria for the actual embedding, including the two R4 figure families. | The host isomorphisms used by catalogue recognition. |
| Sections 7–8 | The local reductions and smaller-pair projection give the constituent shapes at every selected root. | Gardiner's homogeneous graph recognition, the homogeneous two-graph order consequence, locally triangular recognition, and the small rank-three parameter and model lists. |
| Classical and exceptional | Rank-two polar cases, nonsingular orthogonal and unitary cases, and the exceptional reductions. The local obstructions for the 45-vertex unitary graph are checked in Lean. | Published model, parameter and full-group data where used. Both order-40 polar models use the finite rooted certificate. |
| One-dimensional affine | The semilinear cutoff, its small endpoint models, and the exceptional-action exclusions. | Published full affine actions, stabilizer bounds and model identities. The local screening theorem also takes the four Paley exclusions. |
| Extraspecial and exceptional affine | All 40 parameter rows have checked reductions. | Published model and action data for the rows where the parameter screen alone does not suffice. |
| Nontriangular sporadic | The parameter screens and the Mathieu and Higman–Sims reductions. | Published graph identities and full stabilizer orders as needed. |
| Exhaustive rank-three recognition | The theorem applies every supplied model's checked reduction. | `PublishedRankThreeGraphCoverage` remains an explicit premise. Every primitive rank-three host must have the required model and model-specific data. |
| Finite inputs | The exclusions and figure classifications transport to actual embeddings and complement orientations. | Four exact orthogonal and affine-orthogonal exclusions, the order-40 rooted certificate and the Clebsch and Schläfli figure classifications. The separate solver audit for Clebsch and Schläfli is deferred. |

The R17 review packet contains patches against the frozen manuscript and the
preceding proposal, LaTeX diffs, proof notes, and the prior-corrections register.
It includes the correction to Case 4(e), which specifies the matching of
corresponding vertices.
