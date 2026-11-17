# External assumptions for primitive EPPA classification

The primitive theorem concerns a finite transitive primitive host, a particular
induced embedding, and the requirement that the selected graph have at least
half the vertices of the host. Its remaining theorem parameters are listed
below. [Lean endpoint](https://github.com/janhubicka/EPPA-III/blob/946ec067b757eb65b2969322235c5f038836ff49/EPPAIII/Primitive/PublishedRankThreeCoverage.lean#L64)

| Parameter | Input |
|---|---|
| `PublishedRankThreeGraphCoverage` | Every primitive rank-three graph is isomorphic up to complement to one of the fixed models or to a model with the data for a checked reduction. This includes the geometric, strongly regular and full-stabilizer data required for each model. The order-40 cases include the finite rooted certificate. |
| `PrimitiveRecognitionInputs` | Gardiner recognition for finite nonempty homogeneous graphs, locally triangular and locally complement-triangular recognition in both orientations, and the small rank-three parameter and model lists. The order-six-or-ten two-graph consequence is proved from Gardiner. |
| `OrthogonalSearchChecks` | Negative half-order EPPA results for the four exact models `O₆⁺(2)`, `NO₆⁻(2)`, `VO₆⁺(2)` and `VO₆⁻(2)`. |
| `SmallPaleyExclusions` | Negative half-order EPPA results for the Paley models of orders 17, 25, 37 and 41. The exact checker `checks/primitive_small_paley.py` proves the bounds by rooted refinement without requiring full-group orders. |
| `PrimitiveFiniteChecks` | The exact Clebsch and Schläfli figure classifications, including the EPPA assertions for the model selections and coverage of actual embeddings. The separate solver audit is deferred. |

The [full fixed-embedding classification](https://github.com/janhubicka/EPPA-III/blob/main/EPPAIII/Primitive/SmallWitnessNamedClassification.lean)
also uses `NamedTaylorFiniteChecks`, the homogeneity of the two concrete
nontrivial two-graphs. The checker `checks/check_named_taylor_models.py`
verifies these facts and their host and switching-class identities.

The [source-data formulation](https://github.com/janhubicka/EPPA-III/blob/main/validation/primitive/PublishedRecognitionSources.md)
recovers the adjacent codegree from the other three SRG parameters and checks
the numerical small-model screen. The EPPA reductions cover all 21 oriented
rows using the named models. Lean derives nine of the identities from
parameters, rank three or complementation. The published source supplies
the labelled permutation actions for nine further rows and the direct graph
identities for three orthogonal rows. Lean also derives the order-256 point bound.
The [orbital-action adapters](https://github.com/janhubicka/EPPA-III/blob/main/validation/primitive/OrbitalCatalogue.md)
recover graph models up to complement from labelled rank-three actions and
identify the full graph automorphism group with the 2-closure.

## Rank-three catalogue

The coverage premise uses the **full** graph automorphism group. Rank three
asks for vertex transitivity and transitivity on each of the nonempty ordered
edge and ordered distinct nonedge sets. Primitivity says that each invariant
equivalence relation is equality or universal. The recognition data concern
the ambient model and its action and are independent of the actual selected
embedding. The Lean theorem proves the case reduction once those data are
supplied. [Main statement and proof map](Primitive-classification)

The catalogue comes from Brouwer and Van Maldeghem, *Strongly Regular Graphs*,
Chapter 11. Both complementary orbital graphs are relevant. Distinct graph
models can have the same parameters, as in the two graphs with parameters
`(256,45,16,6)` in §10.57. An isomorphism requires separate model recognition.
An upper bound on a full graph stabilizer requires the full group, a proved
embedding of it, or an independent bound. [Catalogue source](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

| Source | Catalogue entries |
|---|---|
| §11.2, affine case A2 | Square rook graphs. |
| Theorem 11.3.1 | Triangular graphs and the individual 35-, 126- and 120-vertex alternating models. |
| Theorems 11.3.2–11.3.3 | Classical polar and Grassmann models and individual classical graphs. |
| Theorem 11.3.4 and Table 11.2 | Exceptional simple-socle models, including the `E₆,₁(q)` graphs. |
| Theorem 11.3.5 and Table 11.3 | Sporadic simple-socle models, including triangular repeats. |
| Theorems 11.4.1–11.4.2 and Table 11.4 | Primitive affine cases A1–A11. |
| Theorems 11.4.3–11.4.4 and Tables 11.5–11.6 | The 40 exceptional and extraspecial affine parameter rows. |

The fixed constructions and the remaining recognized families together form
the Lean catalogue. The R17 review packet gives a source-to-reduction crosswalk.
The graph-only coverage assertion itself remains an external premise.

## Finite checks and validation

The order-40 rooted check concerns the symplectic point graph and the odd
orthogonal line graph. It rules out a selected set of at least 20 vertices
in which every selected root has at least six selected neighbours and the
corresponding rooted local extensions. Lean passes from a half-order EPPA
selection to those conditions. The independent checker is in the R17 review
packet. [Finite predicate and its use](https://github.com/janhubicka/EPPA-III/blob/946ec067b757eb65b2969322235c5f038836ff49/EPPAIII/Primitive/PolarOrderForty.lean#L55)

The small-host screen checks parameter equations and passes exact graph
identities separately. The four orthogonal exclusions and the two positive
figure classifications apply to their named graph models. The proof transports
each result along a host isomorphism and, where applicable, simultaneous
complementation.

The axiom audit checks proof dependencies. The external recognition and finite
results in the table remain explicit theorem hypotheses. [Integrated CI](https://github.com/janhubicka/EPPA-III/actions/runs/44106831662)
