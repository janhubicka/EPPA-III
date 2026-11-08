# EPPA III — complete EPPA obstacle classification for Taylor(C5)

**Review note, 8 November 2026.** The frozen manuscript's arbitrary-double-cover item is false even for vertex-transitive Taylor doubles with invariant mate pairs. The ten-vertex Taylor double of C5 admits a precise replacement.

Let `H` have vertices `(b,x)`, `b in {0,1}`, `x in Z/5Z`, with adjacency `x!=y and (b==c iff x~y in C5)`. Denote its layers `L0`, `L1`.

**Theorem.** For every actual selected subset `S`, `H` is an EPPA witness for the induced `H[S]` if and only if `|S|<=2` or `S subset L0` or `S subset L1`.

**Uniform proof.** Every distinct same-layer pair has exactly 1 common neighbour in the host. Cross-layer pairs over distinct base points have 2, and mate pairs have 0. A mixed-layer triple containing a mate pair has two nonedges with different counts. Otherwise write it as `(0,x),(0,y),(1,z)` for three distinct base vertices. If both cross-layer pairs had the opposite adjacency status to the same-layer pair, then `{x,y,z}` would be a triangle or an independent triple in C5, which is impossible. Hence a cross-layer pair and the same-layer pair have the same adjacency status but different host common-neighbour counts. The corresponding two-point partial isomorphism cannot extend. Thus every EPPA subset of order >=3 lies in a single layer. Conversely, C5 is homogeneous, so all subgraphs of a layer inherit EPPA via diagonal dihedral automorphisms. For any pair of selected vertices, the appropriate dihedral reflection, composed with the deck involution if layers differ, swaps the two vertices and extends every partial map of that pair.

**Exact consequences.** Minimal EPPA obstructions are *all* mixed-layer triples: `C(10,3)-2*C(5,3)=100`, in six full-automorphism orbits. The maximal EPPA subsets are exactly the two 5-vertex layers and the 25 mixed-layer two-point subsets: 27 total, in four orbits. All 1024 subsets were checked directly; 88 have EPPA. The full group has order 20: the displayed dihedral/deck group supplies 20 automorphisms, and a vertex stabilizer injects into the automorphisms of the induced P4 on its four neighbours (order <=2), since the remaining vertices have distinct adjacency signatures to those neighbours.

The finite check is additional evidence; the proof above is uniform. This theorem is **not** a Lean proof and should not cause the original unrestricted first obstacle bullet to be marked green. No manuscript or old TODO was changed.
