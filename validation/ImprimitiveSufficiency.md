# Imprimitive host sufficiency

`ImprimitiveSmallModelSufficiency.lean` constructs extension automorphisms for each named five-cycle and rook model. `ImprimitiveNamedSufficiency.lean` applies those results to every case of `ImprimitiveHostModels`. Both use the designated base embedding in their conclusions.

## Canonical lifts

- For a disjoint double, extend the partial automorphism inside the chosen homogeneous copy and fix the other copy.
- For matching models, apply the same base automorphism to each layer. This preserves the equality of the coordinates of matched vertices, including the corresponding-vertex matching between the rook graph and its complement. A graph automorphism also preserves distinct nonadjacency, so the same coordinate action works when upper adjacency or the rook cross relation is complemented.
- For the two five-cycle models with two cross-neighbours, index each upper vertex (y) by its lower pair ({y,y+d}), where (d=1) or (2) according to the model. A lower translation (xmapsto a+x) acts by the same translation above. A lower reflection (xmapsto a-x) sends the displayed pair to the one indexed by (a-y-d). The shifted upper reflection preserves the upper cycle. The Lean proof derives these two forms of five-cycle automorphism from the images of the first two adjacent vertices. Once those images are fixed, each consecutive vertex is the unique other neighbour. The finite adjacency checks use kernel-checked `decide`.
- For the two-clique construction, encode a vertex ((b,x)) by ((boplus c(x),x)). In those coordinates, adjacency is determined by equality of clique colours and, when present, equality of matching coordinates. Fixing one selected vertex shows that a partial automorphism changes the colours of all selected vertices by the same Boolean offset. Apply that colour change and the prescribed coordinate permutation in the encoded graph, then return to the layer coordinates. A selected vertex stays in the lower layer and has exactly the prescribed image.
- The equal-clique case invokes the existing uniform-cover and Wagner EPPA proofs. All model relabellings conjugate host automorphisms and carry the canonical lower embedding to the designated embedding. The self-complementary cycle and rook cases use the existing explicit complementing permutations.

## Scope

The conclusion is the EPPA property for each case of `ImprimitiveHostModels`. Transitivity, nonhomogeneity, and invariant blocks are hypotheses of the accompanying necessity theorem. The broader model list in `GeneralImprimitiveHostModels` has a Taylor branch with a necessary orbit condition. The separate all-transversals theorem gives Taylor sufficiency under homogeneity of the associated two-graph.

## Validation

Lean 4.35.0-rc3 checked a single-file assembly of the new modules and the exact project declarations used by them, including the existing C5 and rook homogeneity proofs and the uniform-cover and Wagner sufficiency proofs. The axiom audit of the seven sufficiency endpoints reports the standard `propext`, `Classical.choice`, and `Quot.sound`. The whole-package import build is a separate integration check.
