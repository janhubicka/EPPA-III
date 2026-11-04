import EPPAIII.CliqueCovers.NoInducedFive

/-!
# Complements of generalized clique covers contain no induced five-cycle

The self-complementarity of C₅ is used in its explicit five-vertex form.
If (a,b,c,d,e) induces C₅ in the complement of a cover, then the
reordered tuple (a,c,e,b,d) induces C₅ in the cover itself.

The result is valid for all parameters s,t, with no positive-size
hypotheses or classification input. The five distinctness assumptions
correspond exactly to the pairs that are nonadjacent in the alleged
complement cycle; the other five inequalities follow from its edges.
-/

namespace EPPAIII.CliqueCovers

/-- A generalized cover's complement also excludes induced five-cycles.

The theorem is stated with the literal SimpleGraph complement, so it
can be used directly when an exceptional host is classified only up
to simultaneous graph complementation. -/
theorem cover_complement_no_induced_five_cycle
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (a b c d e : CoverVertex s t)
    (hab : (coverGraph s t X Y)ᶜ.Adj a b)
    (hbc : (coverGraph s t X Y)ᶜ.Adj b c)
    (hcd : (coverGraph s t X Y)ᶜ.Adj c d)
    (hde : (coverGraph s t X Y)ᶜ.Adj d e)
    (hea : (coverGraph s t X Y)ᶜ.Adj e a)
    (hnac : ¬ (coverGraph s t X Y)ᶜ.Adj a c)
    (hnad : ¬ (coverGraph s t X Y)ᶜ.Adj a d)
    (hnbd : ¬ (coverGraph s t X Y)ᶜ.Adj b d)
    (hnbe : ¬ (coverGraph s t X Y)ᶜ.Adj b e)
    (hnce : ¬ (coverGraph s t X Y)ᶜ.Adj c e)
    (hneac : a ≠ c) (hnead : a ≠ d)
    (hnebd : b ≠ d) (hnebe : b ≠ e) (hnece : c ≠ e) :
    False := by
  change a ≠ b ∧ ¬ coverAdj X Y a b at hab
  change b ≠ c ∧ ¬ coverAdj X Y b c at hbc
  change c ≠ d ∧ ¬ coverAdj X Y c d at hcd
  change d ≠ e ∧ ¬ coverAdj X Y d e at hde
  change e ≠ a ∧ ¬ coverAdj X Y e a at hea
  change ¬ (a ≠ c ∧ ¬ coverAdj X Y a c) at hnac
  change ¬ (a ≠ d ∧ ¬ coverAdj X Y a d) at hnad
  change ¬ (b ≠ d ∧ ¬ coverAdj X Y b d) at hnbd
  change ¬ (b ≠ e ∧ ¬ coverAdj X Y b e) at hnbe
  change ¬ (c ≠ e ∧ ¬ coverAdj X Y c e) at hnce
  have hac : coverAdj X Y a c := by
    by_contra h
    exact hnac ⟨hneac,h⟩
  have had : coverAdj X Y a d := by
    by_contra h
    exact hnad ⟨hnead,h⟩
  have hbd : coverAdj X Y b d := by
    by_contra h
    exact hnbd ⟨hnebd,h⟩
  have hbe : coverAdj X Y b e := by
    by_contra h
    exact hnbe ⟨hnebe,h⟩
  have hce : coverAdj X Y c e := by
    by_contra h
    exact hnce ⟨hnece,h⟩
  exact cover_no_induced_five_cycle X Y a c e b d
    hac hce (coverAdj_flip X Y b e hbe) hbd
    (coverAdj_flip X Y a d had)
    (by intro h; exact hea.2 (coverAdj_flip X Y a e h))
    hab.2
    (by intro h; exact hbc.2 (coverAdj_flip X Y c b h))
    hcd.2
    (by intro h; exact hde.2 (coverAdj_flip X Y e d h))
    hea.1.symm hab.1 hbc.1.symm hcd.1 hde.1.symm

end EPPAIII.CliqueCovers
