# Four small Paley exclusions

`python3 checks/primitive_small_paley.py` verifies the finite bounds below by colour refinement of the explicit Paley models used in `SmallConstituentModels.lean`. It uses Python's standard library and exact integer arithmetic and also checks the expected strongly regular parameters.

| Host order | Second anchors | Largest final class outside the anchors | EPPA order bound | Half-order threshold |
| ---: | ---: | ---: | ---: | ---: |
| 17 | 16 | 1 | 6 | 9 |
| 25 | 24 | 2 | 10 | 13 |
| 37 | 36 | 1 | 6 | 19 |
| 41 | 40 | 1 | 6 | 21 |

For the prime orders, the vertex labels are residues and adjacency is the distinct-vertex square-difference test modulo the order. For order 25, vertices are pairs modulo 5 and the square set consists of the pairs \((a^2+2b^2,2ab)\). Both orientations of the difference appear in each model's test. Translation by the negative of the first anchor is a graph automorphism because it preserves differences. The checker fixes that anchor at zero and checks every other vertex as the second anchor.

For anchors \(a,b\), the initial colour of a vertex records whether it equals each anchor and whether it is adjacent to each anchor. A refinement step replaces its colour by its previous colour and the counts of its neighbours in every previous colour class. An automorphism fixing \(a,b\) preserves the initial colours. If it preserves the previous colours, its bijection between the two neighbourhoods preserves their counts in each previous colour class. Induction therefore shows that it preserves all final colours. The checker assigns colour identifiers by first occurrence in vertex order. Each step refines the previous partition, so the process terminates on the finite vertex set.

Choose two anchors in any EPPA selection \(S\) of size at least two. For two vertices of \(S\) outside the anchors with equal adjacency profiles into the anchors, the map sending one vertex to the other and fixing both anchors is an isomorphism on those induced three-vertex subgraphs. An extension to the host fixes the anchors, so the two vertices have the same final colour. All selected vertices of that adjacency profile therefore lie in one final colour class. For each of the four profiles, the checker computes the largest class it could contribute, then adds two for the anchors. This bounds the order of \(S\) and establishes the four statements in `SmallPaleyExclusions` as finite computational checks.
