## Wagner exceptional EPPA sufficiency — 18 October 2026

The frozen source's Lemma 6.1 identifies the Wagner eight-vertex graph as the exceptional possible host of the selected 2K₂. The previously verified *necessary* classification did not in itself prove this graph is an EPPA witness.

The canonical Wagner graph is a Möbius ladder whose cyclic order in the source's Bool × (Fin 2 × Fin 2) coordinates is 000, 100, 010, 110, 001, 111, 011, 101 (first digit is the side). Its eight cycle edges and four antipodal chords are invariant under the sixteen permutations k ↦ a+k and k ↦ a-k (modulo 8). An exact finite audit of each partial automorphism of the designated 2K₂ shows extension by one of those sixteen symmetries.

The new Lean theorem is `EPPAIII.CliqueCovers.wagnerCanonicalGraph_isEPPA`. The author manuscript is not edited. This does not validate the original proof prose verbatim, nor any external graph classification.

The EPPA proof passed the full Lean build, permitted-axiom audit, and finite checks in CI run 39156609457. The additional exact vertex-transitivity certificate uses only the eight cyclic rotations of the canonical Wagner graph and is audited on the same branch (new CI pending). The source manuscript is unchanged.
