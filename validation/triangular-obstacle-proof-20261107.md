# EPPA III — general triangular-graph obstacle proof (7 November 2026)

**Manuscript:** `main-new(20261031-234151).tex`, item 2 of
`thm:obstacles`. **Scope:** a paper-level proof for **n ≥ 5** and a
separate Lean proof of the hereditary EPPA interface. No author manuscript
text, existing TODO, or previously commented-out note is changed.

## Statement

Let `T(n) = L(K_n)` for `n ≥ 5`. For an induced graph
`G ⊆ T(n)`, the ambient graph `T(n)` is an EPPA witness for this
**particular embedding** of `G` if and only if `G` contains neither

1. an induced diamond `O_4 = K_4 - e`; nor
2. an induced `2 K_3` whose two component triangles have opposite
   focus types in the ambient `T(n)`.

A focused triangle consists of three edges of `K_n` through one
underlying point; an unfocused triangle consists of the three edges
of a triangle in `K_n`.

## Proof (combinatorial; not yet formalized in Lean)

**Ambient automorphisms.** The maximal cliques of size `n-1≥4`
in `T(n)` are precisely the `n` stars of edges through a point
of `K_n`. Any ambient automorphism permutes those stars, and the
vertex `{i,j}` is uniquely determined by the intersection of the
stars at `i` and `j`. Hence `Aut(T(n)) = Sym(n)`. In particular,
an ambient automorphism cannot turn a focused triangle into an
unfocused triangle.

**Mixed triangles force one listed obstruction.** Let `U` be an
unfocused triangle corresponding to the three pairs of a set
`A={a,b,c}`, and `F` a focused triangle of three pairs through
`p`. If `p∈A`, at least one member of `F` is not a member of
`U`; it is adjacent to exactly two members of `U`, yielding
an induced diamond. If `p∉A`, but a leaf of `F` lies in `A`,
that leaf's incident pair likewise meets exactly two members of
`U`, again yielding an induced diamond. Otherwise all pairs in
`F` are disjoint from all pairs in `U`, so `F∪U` induces
`2K_3`, with opposite focus types. Conversely, each induced
diamond in `T(n)` has one focused and one unfocused triangle.
Thus both listed configurations obstruct EPPA by a partial
isomorphism of their triangles.

**Incidence reconstruction lemma.** Consider two ordered lists of
distinct two-subsets of a common n-element set. If corresponding
pairs intersect in exactly the same pattern, and corresponding
triples have a common underlying point in exactly the same pattern,
then there is one permutation of the ground set carrying each pair
of the first list to the corresponding pair of the second. To see
this, an intersecting pair of selected edges identifies its
unique common endpoint. The maximal collection of selected
edges through this endpoint consists exactly of the two chosen
edges together with those third edges forming a focused triple
with them. Hence the pairwise data and focused-triple indicators
identify every ground point incident with at least two selected
edges and all its incident edges. After those shared points are
matched, each selected edge has the same number (zero, one, or two)
of remaining *private* endpoints in the two lists; match them
individually. Finally match the unused ground points. This gives
the required permutation.

**Sufficiency.** Suppose `G` avoids both forbidden induced
configurations. The mixed-triangle lemma shows that all triangles
in `G` have the same ambient focus type (or there are none).
Any partial isomorphism of `G` preserves pairwise intersection
of its corresponding `K_n`-edges; it also preserves whether any
three of them meet at one ground point, because those triples form
triangles of the same focus type in `G`. The reconstruction lemma
gives a permutation of `[n]` inducing the partial isomorphism,
and this extends to an automorphism of `T(n)`.

This proof **requires n ≥ 5**. At n=4, T(4) is the octahedron and
has automorphisms not induced by Sym(4); the existing author TODO
documents the counterexamples.

## Independent finite checks

* For `n=5,6,7,8`, every pair consisting of one focused and one
  unfocused triangle has an induced diamond or an induced opposite-focus
  `2K_3`. For `n=8` this covered 15,680 pairs.
* For all 54,264 six-vertex induced subgraphs of `T(7)`, the
  forbidden-pattern criterion agrees with full extension of every
  partial isomorphism through `Sym(7)`: 29,834 avoid both obstructions
  and all 29,834 satisfy EPPA.
* A separate orbit reconstruction regression tested all 39,070,080
  ordered six-tuples of pairwise distinct edges in `K_7`. Among
  9,148 adjacency-plus-focus types, no type split into different
  underlying incidence orbits.

The finite tests are adversarial evidence; the unrestricted proof
above is the reconstruction argument, not extrapolation from them.

## Lean boundary

`EPPAIII/EPPA/Hereditary.lean` formalizes that a verified EPPA
embedding remains EPPA after restricting the *selected base* to any
induced embedded subgraph. The companion `EPPAIII/EPPA/InducedSubsetEPPA.lean` specializes
this to literal vertex subsets of a fixed host and proves downward closure
of EPPA and upward closure of failure. The new
`EPPAIII/EPPA/IncidenceSignature.lean` establishes unique shared
endpoints for distinct two-point edges and derives their entire indexed
incidence signatures from focused-triple data in Lean, including transport
to a second edge family with the same intersection and focus records.
This does **not** yet build the global ground-point permutation, formalize
the mixed-triangle obstruction, or establish the triangular classification.
Each new declaration is registered in `CheckAxioms.lean`, but must not
be described as CI-verified until the current branch passes its workflow. The general triangular proof is paper-level until
those geometric/incidence lemmas are represented in Lean.

## Editorial policy

The previously commented-out author notes, the existing `T(4)`
TODO, and the paper's other obstacle theorem items are preserved.
Propose separately a one-word statement repair (insert `n ≥ 5`)
and the proof above as a localized diff against the frozen source.
