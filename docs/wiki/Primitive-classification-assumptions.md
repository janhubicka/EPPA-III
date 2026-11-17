# External assumptions for primitive EPPA classification

## Rank-three catalogue

The external classification premise takes a finite simple graph whose **full** automorphism action is primitive and rank three. Its conclusion is a graph isomorphism to one of the listed models, in one of the two complementary orientations. Lean's `HasRankThreeAutAction` asks for a nonempty ordered edge orbit and a nonempty ordered distinct nonedge orbit, and transitivity on the vertices and each of those two pair sets. `IsPrimitiveAutAction` states that each invariant equivalence relation is equality or universal.

The premise has no selected subgraph, half-order bound, EPPA condition, or claim about which cases the manuscript eventually excludes. `small_primitive_eppa_in_rankThreeCatalog` takes the premise as a parameter and applies it after deriving the three-way reduction. See [the main statement and proof map](Primitive-classification).

The source for the catalogue is Brouwer and Van Maldeghem, *Strongly Regular Graphs*, Chapter 11. Graphs can appear under multiple groups. Both of their complementary orbital graphs are candidates. For example, the two graphs in §10.57 have the same parameters `(256,45,16,6)`. The half folded 10-cube and the bilinear forms graph `H₂(4,2)` require separate identities. The order of a point stabilizer in a subgroup from Chapter 11 is not an upper bound on the order of the full graph automorphism stabilizer. Any argument needing that upper bound requires a full automorphism identification, an explicit embedding of the full group, or an independently verified bound. [Source](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

| Source | Catalogue entries |
|---|---|
| §11.2, affine case A2 | Square rook graphs. |
| Theorem 11.3.1 | Triangular graphs and the individual 35-, 126- and 120-vertex alternating-socle models. |
| Theorems 11.3.2–11.3.3 | Classical models on singular points, maximal singular subspaces, nonsingular points or hyperplanes, Grassmann graphs, and the individual classical models. |
| Theorem 11.3.4 and Table 11.2 | Exceptional simple-socle models, including the `E₆,₁(q)` graphs. |
| Theorem 11.3.5 and Table 11.3 | Sporadic simple-socle models, including triangular repeats. |
| Theorems 11.4.1 and 11.4.2, Table 11.4 | Primitive affine cases A1–A11, including semilinear and classical families. |
| Theorems 11.4.3 and 11.4.4, Tables 11.5–11.6 | Exceptional and extraspecial affine models. |

The Lean interface fixes the rook, triangular and three individual alternating models. Its remaining `RankThreeCatalog` entries are parameters for families of exact graph models. This interface is only a checkpoint. An independent verification must compare each residual family and admissible parameter range with its source and instantiate the catalogue before using it for case elimination. For example, filling a residual catalogue row with every finite graph would make the premise trivial and would give no valid coverage claim for the paper. The final reviewed theorem must name or construct each model and account for every catalogue row. Assumptions about local actions, graph identities and graph parameters also need their own source locations or proofs.

## Other inputs in the manuscript

The table lookup for small strongly regular hosts in R17 uses Table 11.8 and both complementary orientations. The parameter equation is an arithmetic screen. Exact graph identity and actual subconstituent type are separate checks when two graphs share a parameter set. The numerical search must carry a proved upper bound on host order and cover the complete source range.

Section 7 invokes Makhnev and Hall for locally triangular and locally complement-triangular graphs. These local recognition theorems are separate from the rank-three classification. Their exact hypotheses and lists must be recorded before using them in the final theorem. The homogeneous branch also uses Gardiner's finite homogeneous graph classification, separately from Chapter 11. No placeholder for a missing family exclusion belongs in the rank-three premise.

## Finite computations

The four negative EPPA inputs in the proposed interface are four exact orthogonal graph models, each considered with its given adjacency or its simultaneous complement:

| Graph | Order | Input |
|---|---:|---|
| `O₆⁺(2)` | 35 | Singular projective points of the split quadratic form, with polar-form collinearity. |
| `NO₆⁻(2)` | 36 | Nonsingular points for the minus-type quadratic form. |
| `VO₆⁺(2)` | 64 | Affine points for the plus-type quadratic form. |
| `VO₆⁻(2)` | 64 | Affine points for the minus-type quadratic form. |

For a listed model `H`, the negative input says that every fixed induced embedding `e : G ↪ H` with `|H| ≤ 2|G|` fails `IsEPPAEmbedding G H e`. The theorem parameters should name the four models individually. A tuple of strongly regular parameters alone cannot replace a model. The plus affine graph appears in both orientations in the manuscript. The orientation transfer complements both host and base. The manuscript's mention of a computational treatment for `complement(NO₃⁺(8))` is repaired using its identity with `complement(T(9))`. See §3.1.4 of the monograph. [Source](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

The nine actual isomorphism occurrences in the 30-row small-subconstituent parameter screen are an independent consistency check. The exhaustive table membership used by the proof is a different claim. Positive finite witness classifications for the figure models require separate, exact checks. The four negative inputs cannot establish either claim.

## Review checklist

- Inspect the theorem types and `CheckAxioms.lean`. Read each explicitly passed hypothesis as a separate mathematical obligation.
- Check that the covering premise has the correct primitive-action and graph isomorphism scope, and that the source exhausts the precise instantiated catalogue.
- Review complement orientation, odd-order rounding and the fixed embedding in each case.
- Reproduce finite inputs from the exact adjacency data and record the input, version, and negative certificates. A graph name, order or parameter row alone does not certify an EPPA exclusion.
