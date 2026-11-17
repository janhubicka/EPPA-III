# Recognition inputs to the small-witness classification

[`smallWitnessNamedModelCases_iff_eppa_of_published_sources`](../../EPPAIII/Primitive/PublishedRecognitionAssembly.lean)
uses the same fixed-embedding model list as the existing classification.
Its recognition record gives the published data before the transport and
arithmetic performed in Lean.

| Input | What Lean derives |
| --- | --- |
| Gardiner's finite homogeneous graph classification on nonempty `Fin n` | The selected, host, and descendant forms at any finite vertex type and in either universe. |
| Main rank-three catalogue on `Fin n` | Transport to the actual host's labels, including `IsPrimitiveAutAction` and `HasRankThreeAutAction`. |
| One Table 11.8 row per small graph, with `(v,k,μ)` | The adjacent codegree `λ` from the SRG equation and the exact oriented row. The pentagon gives `λ=0`. Equal valency can still give different adjacent and nonadjacent codegrees after complementation. |
| Labelled rank-three actions on the five triangular and four Paley rows, plus the three orthogonal isomorphisms on `Fin n` | All 21 oriented matches in the small screen. Lean reconstructs Clebsch, Schläfli's complement, and all six rook rows. For `T(7)`, the adjacent codegree distinguishes the orientations even when valencies agree. |
| The connected locally triangular and locally Kneser lists, with the Mathieu bound at one root | Both host orientations by primitivity and the rank-three action. The order-256 point bound follows internally from the local triangular model. Point conjugation moves the order-2048 bound to every root. |

The full catalogue includes graph and full-action data needed for its particular family. New constructors take a single chart for either of the two higher polar calculations, the two constituents at one root for the binary polar calculation, or the local clique-extension model for `E₆`. The latter gives connectedness because the half-spin graph is connected. For the binary unitary, odd nonsingular orthogonal, and projective half-spin models, a host isomorphism up to complement transfers the transitive action. This avoids a separate proof of transitivity for the model in each invocation.

For a rank-two polar graph, a line of size `q+1`, the SRG parameters and ordered-edge transitivity yield the local chart. At each local vertex, transport a line through the corresponding host edge and delete the root. The remaining `q` vertices exhaust that local vertex's closed neighbourhood by its degree `q-1`. These neighbourhoods give a partition into cliques. The same argument with local degree one gives the local matching of the Berlekamp–Van Lint–Seidel graph directly from its parameters. A published upper bound for the full automorphism group gives the point bound by orbit–stabilizer.

The Clebsch recognition is a graph isomorphism statement. The five neighbours of a root are independent, and each pair has exactly one further common neighbour. Every nonneighbour of the root arises once in this way. The resulting 16 labels match the four-bit graph. Its previously checked EPPA subgraphs are still a finite input to the classification.

The small-constituent proof has a checked reduction for each of its 21 oriented parameter rows. Eight of the 20 printed model identities follow from the parameters and, for rook, rank three. The extra orientation of the four-by-four rook graph follows by complementation. There are nine further identities derived in Lean from the labelled permutation actions in the literature. On triangular models the action comes from point permutations on two-element sets. On Paley models it comes from square semilinear maps of the field. For the 35-, 36-, and 64-vertex orthogonal entries the input gives the graph isomorphisms directly. These identities allow the exclusions or classifications for the named models to be applied to the actual embedding.

The Schläfli uniqueness proof uses the parameters `(27,10,1,5)`. The neighbours of a root form five matched pairs. The 16 distinct nonneighbours of the root are labelled by the even-parity words that record one choice from each pair. In their induced graph, adjacency flips four coordinates. The resulting chart fixes the graph up to isomorphism and applies to the explicit double-six model. The already checked EPPA figure result is a distinct finite input. [Brouwer and Van Maldeghem, §10.10](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf)

For the order-256 bound, two nonadjacent vertices with a common neighbour have four common neighbours inside the triangular graph at that neighbour. The SRG has six common neighbours in total. This makes the neighbourhood signatures of distinct nonneighbours of a fixed root different. Its point stabilizer therefore acts faithfully on the copy of `T(10)`, whose ten stars bound the automorphism group by `10!`.

The main catalogue still needs the exhaustive graph, chart, and full-group bridge from Chapter 11. The Table 11.8 coverage and named source identities are also mathematical inputs, alongside the cited local recognition theorems. The finite EPPA inputs remain explicit. [Brouwer–Van Maldeghem, Strongly Regular Graphs](https://homepages.cwi.nl/~aeb/math/srg/rk3/srgw.pdf) · [Makhnev, Proposition 1](https://www.mathnet.ru/eng/timm328)

Rows given by permutation representations can use the [orbital-action adapters](OrbitalCatalogue.md) to derive the graph model and its full automorphism action.
