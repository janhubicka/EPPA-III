# Certificates for the four binary finite exclusions

Run `python3 checks/section8_binary_negative.py` from the repository root. The verifier reads [compressed explicit witnesses](../../checks/section8_binary_negative_certificate.txt.gz) using the Python standard library. Its two six-dimensional quadratic forms agree with [the Lean definitions](../../EPPAIII/Primitive/BinaryOrthogonalModels.lean).

| Point model | Order | Extension rules | Parity obstructions | EPPA order upper bound |
|---|---:|---:|---:|---:|
| O6+ | 35 | 13,053 | 9,053 | 16 |
| NO6+ | 28 | 7,214 | 3,996 | 16 |
| O6− | 27 | 15,063 | 5,852 | 16 |
| NO6− | 36 | 12,951 | 9,183 | 16 |

For a subset of the host, the property that every vertex has an even number of distinct nonneighbors in the subset is invariant under host automorphisms. Isomorphic induced pieces with different parity values give a partial automorphism that cannot extend. The verifier checks both values in the full host and checks the induced graph isomorphism.

The certificate starts with the empty representative. At each order through 17, it accounts for every one-vertex extension of every retained representative. A rule retains the extension, maps an earlier representative to it via a word in checked automorphisms, or gives an explicit parity obstruction. The level-17 lists are empty. The induction uses heredity of EPPA within a fixed host and invariance under host automorphisms. The available generators only need to be genuine automorphisms.

For either affine graph, translate a selected root to zero. The neighbours and distinct nonneighbours are the two corresponding point graphs. An order-32 EPPA selection therefore gives every selected vertex degree 15 or 16. Normalize the selected neighbours of zero using the verified linear generators. Enumerate their products with all images of the retained distinct-nonneighbour representatives. A selected vertex violates the degree bound in each of the 686 plus-type and 1,080 minus-type candidates. Larger selected orders reduce to 32 by heredity.

This independently reproduces the four finite inputs of `OrthogonalSearchChecks` on the exact models. The Lean transport and parity lemmas formalize the implications used by the search. Kernel verification of the entire point certificate is a separate obligation.
