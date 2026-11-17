# Alternating forms graph repair

The patch replaces the proof of Lemma `lemma:alternatingforms` in the frozen
R17 source `main-new(20261116-151839)-markers-r17.tex`. Apply it from the
directory containing that file with `git apply EPPAIII-R17-alternating-five.patch`.
The full marked-up source and a compiled changed-page preview are included.

The replacement computes both constituent profiles from the displayed
strongly regular parameters. For each, the degree is greater than one and
below half the order minus one. Moreover, its order is odd or exceeds
four times the degree, and none of the degree and the next two integers
divides the order. The patch gives both quotient–remainder identities
and their strict remainder bounds.

These checks exclude all four forms in the minimal-counterexample
hypothesis. For plain covers they use the four possibilities for the
diagonal cross block. For complemented covers they use even order and
the quarter-order lower bound on any degree greater than one. The argument
removes the connectivity assertion, the automorphism-group order estimate
and the Stirling bound from this lemma.

The corresponding Lean arithmetic is in
`EPPAIII/Primitive/AlternatingFiveArithmetic.lean`. The graph theorem
`EPPAIII.Primitive.alternatingFive_constituent_exclusion` in
`EPPAIII/Primitive/AlternatingFiveExclusion.lean` uses the constituent order
and degree as hypotheses. The theorem
`EPPAIII.Primitive.alternatingFive_excludes_actual_constituents` checks the
constituent profiles of an actual rooted host with those strongly regular
parameters. Identification of the alternating forms graph with that
parameter tuple comes from Brouwer–Van Maldeghem, Section 3.4.2.
