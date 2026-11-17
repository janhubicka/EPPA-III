# Finite cases in the primitive classification

`BinaryOrthogonalModels.lean` defines the adjacency actually passed to the finite-search assumptions. `FiniteExclusions.lean` states the four assumptions through the maximum cardinality of a vertex subset satisfying `IsEPPAEmbedding` via its inclusion into the host. The bound is strict, `2 * maxEppaOrder H < Nat.card W`. This excludes equality when the host order is even and uses the ceiling of half the order when it is odd.

| Lean field | Host measured in standard orientation | Strongly regular parameters | First manuscript use |
| --- | --- | --- | --- |
| `oSixPlus` | Perpendicularity on nonzero singular vectors for the plus form on `Fin 64` | `(35,18,9,9)` | Lemma `lemma:smallconstituents`, in the complementary orientation `(35,16,6,8)` |
| `noSixMinus` | Perpendicularity on nonsingular vectors for the minus form | `(36,15,6,6)` | Lemma `lemma:smallconstituents` |
| `voSixMinus` | Singular difference for the minus form on all 64 vectors | `(64,27,10,12)` | Lemma `lemma:smallconstituents`, in the complementary orientation `(64,36,20,20)` |
| `voSixPlus` | Singular difference for the plus form on all 64 vectors | `(64,35,18,20)` | Lemma on triangular subconstituents, in the complementary orientation `(64,28,12,12)` |

Lean checks all four displayed parameter tuples in `FiniteModelParameters.lean`. It also checks an explicit isomorphism from the complement of `orthogonalSixGraph true true` to `equalBipartitionGraph 3` in `Order35Transport.lean`. That model isomorphism supplies the orientation in `OrthogonalSearchChecks.equalBipartitionThree`.

The coordinate formulas are shared with the prior seven induced-five-cycle certificates. For each host, the coordinates and adjacency relation are fixed independently of the classification and EPPA. The finite induced-cycle certificates alone give no EPPA exclusion. To use a search input under a rank-three classification result, supply a graph isomorphism to the appropriate model. Matching the strongly regular parameters alone is insufficient. Complementing the selected graph and host preserves the fixed embedding and its EPPA property. As a result, a single search assumption per complementary pair suffices.

The four negative outcomes were independently reproduced. [The certificate note](binary-negative-certificate.md) gives the exact checker, its rules and the two affine degree tests. The checker uses integer operations with explicit combinatorial witnesses for each discarded orbit representative. `AffineRootDegreeCertificate.lean` uses kernel reduction to check coverage of the listed local and nonlocal mask products and a selected vertex of wrong degree in each product. The point-orbit coverage and the reduction of every affine witness to a listed mask are still required to discharge the four finite exclusion propositions in Lean.

## The order-126 bipartition graph

`BipartitionTenConstituents.lean` represents a partition of the ten points by the part containing zero. It identifies the local graph at `{0,1,2,3,4}` with the 5-by-5 rook graph by swapping one point from each part. The nonlocal subconstituent has 100 vertices. Within it, `{0,1,2,5,6}` and `{0,1,2,5,7}` are an adjacent pair with six common neighbours, whereas `{0,1,2,5,6}` and `{0,1,5,6,7}` are an adjacent pair with eight. `{0,1,2,5,6}` and `{0,1,2,7,8}` are nonadjacent.

In a half-order selected set of a rank-three host of this type, the rook bound of 11 leaves at least `63 − 1 − 11 = 51` selected nonneighbours of a selected root. Root stabilizer transitivity and EPPA would then force the 100-vertex nonlocal graph to be complete, empty or rank three. The displayed pairs exclude all three outcomes.

`NO_3^+(8)` is `T(9)` by Brouwer–Van Maldeghem §3.1.4, so its complement has a large EPPA subgraph using the triangular theorem. The complement of `NO_3^+(4)` is likewise the complement of `T(5)`. The accompanying manuscript patch records both orientations. [Brouwer–Van Maldeghem, Strongly Regular Graphs](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

## The Clebsch and Schläfli positive models

`ClebschSchlafliModels.lean` fixes the exact host labellings and the lists of five and fourteen maximal orbit representatives at half order. The Clebsch labels are binary vectors in `Fin 16`, with XOR differences in `{1, 2, 4, 8, 15}` defining the edges. The Schläfli labels use a double six in `Fin 27`. The two sixes occupy indices 0 through 5 and 6 through 11. Indices 12 through 26 enumerate the unordered pairs of six indices in lexicographic order.

The archived exhaustive verification was rerun. All six Clebsch and all 22 Schläfli maximal orbit representatives passed every partial-isomorphism extension check. The five and fourteen large representatives in the Lean lists are exactly those of order at least half the corresponding host. The certificate applies to a fixed embedding when its selected set is contained in an automorphic image of one of these representatives. The drawings in the manuscript still require identification with these exact masks. An abstract isomorphism type of the selected graph alone would require a separate argument covering all its embeddings. [Reproducible finite verification](https://chatgpt.com/library?file_id=libfile_fde3_f-3d46bf0fb5688191b9fd82ea85629a77_0b75d3d89e20819199daa9c857464684&account_id=personal)

## Audit checklist

- The EPPA property of a subset is computed using its actual embedding in the host. The equivalence through `maxEppaOrder` quantifies over all such subsets.
- Check failure against the full automorphism group of the host. Nonextendability under an arbitrary subgroup, even one acting with rank three, cannot certify failure under the full group.
- An induced partial isomorphism is tested in both directions, including nonedges. Candidate deduplication under abstract isomorphism alone is unsound before computing the witness property in the given host.
- A breadth-first search can prune by a known failing induced subset. To deduplicate by host orbit, it must either store all orbit images or use verified canonical representatives. The group used for that deduplication must act by actual host automorphisms.
- A genuine finite positive certificate can use a subgroup to exhibit extensions. Showing nonextendability still requires a complete automorphism enumeration or an invariant respected by the full group.
