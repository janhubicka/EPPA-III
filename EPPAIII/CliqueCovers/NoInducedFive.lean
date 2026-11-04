import EPPAIII.CliqueCovers.Basic

/-!
# Uniform generalized clique covers have no induced 5-cycles

A five-cycle in a cover would necessarily use an edge inside one of
the chosen clique cells, because its two side colours cannot alternate
around an odd cycle. Such an edge forces its two external cycle
neighbours into the same opposite-side clique, producing a chord.

The result is formulated using all ten exact pair conditions of an
induced C5, including distinctness of the nonadjacent vertices.
No finite-parameter bound or external classification is assumed.
-/

namespace EPPAIII.CliqueCovers

/-- If a,b belong to the same side and are adjacent, a neighbour
of b which is not a neighbour of a and is distinct from a must be
on the opposite side and in the same clique-index cell. -/
private theorem cover_asymmetric_neighbour_location
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (a b c : CoverVertex s t)
    (hab : coverAdj X Y a b)
    (hSame : a.1 = b.1)
    (hbc : coverAdj X Y b c)
    (hNotAC : ¬ coverAdj X Y a c)
    (hNeAC : a ≠ c) :
    c.1 ≠ a.1 ∧ c.2.1 = a.2.1 := by
  have habIndex : a.2.1 = b.2.1 := by
    rcases hab with ⟨_,hi,_⟩ | ⟨hn,_⟩
    · exact hi
    · exact (hn hSame).elim
  by_cases hACside : a.1 = c.1
  · have hBCside : b.1 = c.1 := hSame.symm.trans hACside
    rcases hbc with ⟨_,hBCindex,_⟩ | ⟨hOpp,_⟩
    · have hACindex : a.2.1 = c.2.1 := habIndex.trans hBCindex
      have hACcoord : a.2.2 ≠ c.2.2 := by
        intro hEq
        exact hNeAC (Prod.ext hACside (Prod.ext hACindex hEq))
      exact (hNotAC (Or.inl ⟨hACside,hACindex,hACcoord⟩)).elim
    · exact (hOpp hBCside).elim
  · refine ⟨Ne.symm hACside, ?_⟩
    by_contra hIndexCA
    have hBCindex : b.2.1 ≠ c.2.1 := by
      intro hBCeq
      exact hIndexCA (habIndex.trans hBCeq).symm
    have hY : Y = true := by
      rcases hbc with ⟨hBCside,_,_⟩ | ⟨_,hCross⟩
      · exact (hACside (hSame.trans hBCside)).elim
      · simpa [hBCindex] using hCross
    have hIndexAC : a.2.1 ≠ c.2.1 := by
      intro h
      exact hIndexCA h.symm
    have hACadj : coverAdj X Y a c :=
      Or.inr ⟨hACside, by simpa [hIndexAC] using hY⟩
    exact (hNotAC hACadj).elim

/-- In a chordless five-cycle, a specified edge must join the
two different sides of the cover. The arguments c,d are the
next and previous vertices along the cycle. -/
theorem cover_induced_cycle_edge_crosses_sides
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (a b c d : CoverVertex s t)
    (hab : coverAdj X Y a b)
    (hbc : coverAdj X Y b c)
    (hda : coverAdj X Y d a)
    (hNotAC : ¬ coverAdj X Y a c)
    (hNotBD : ¬ coverAdj X Y b d)
    (hNotCD : ¬ coverAdj X Y c d)
    (hNeAC : a ≠ c)
    (hNeBD : b ≠ d)
    (hNeCD : c ≠ d) :
    a.1 ≠ b.1 := by
  intro hSame
  obtain ⟨hcSide,hcIndex⟩ :=
    cover_asymmetric_neighbour_location
      X Y a b c hab hSame hbc hNotAC hNeAC
  obtain ⟨hdSide,hdIndex⟩ :=
    cover_asymmetric_neighbour_location
      X Y b a d (coverAdj_flip X Y a b hab)
        hSame.symm (coverAdj_flip X Y d a hda) hNotBD hNeBD
  have hABindex : a.2.1 = b.2.1 := by
    rcases hab with ⟨_,hi,_⟩ | ⟨hOpp,_⟩
    · exact hi
    · exact (hOpp hSame).elim
  have hdSideA : d.1 ≠ a.1 := by
    intro h
    exact hdSide (h.trans hSame)
  have hCDside : c.1 = d.1 := by
    cases ha : a.1 <;> cases hc : c.1 <;> cases hd : d.1 <;>
      simp_all
  have hCDindex : c.2.1 = d.2.1 :=
    hcIndex.trans (hABindex.trans hdIndex.symm)
  have hCDcoord : c.2.2 ≠ d.2.2 := by
    intro h
    exact hNeCD (Prod.ext hCDside (Prod.ext hCDindex h))
  exact hNotCD (Or.inl ⟨hCDside,hCDindex,hCDcoord⟩)

/-- A literal induced 5-cycle cannot occur in a uniform generalized
clique cover, for arbitrary (including degenerate) s,t and cross-types. -/
theorem cover_no_induced_five_cycle
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (a b c d e : CoverVertex s t)
    (hab : coverAdj X Y a b)
    (hbc : coverAdj X Y b c)
    (hcd : coverAdj X Y c d)
    (hde : coverAdj X Y d e)
    (hea : coverAdj X Y e a)
    (hnac : ¬ coverAdj X Y a c)
    (hnad : ¬ coverAdj X Y a d)
    (hnbd : ¬ coverAdj X Y b d)
    (hnbe : ¬ coverAdj X Y b e)
    (hnce : ¬ coverAdj X Y c e)
    (hneac : a ≠ c)
    (hnead : a ≠ d)
    (hnebd : b ≠ d)
    (hnebe : b ≠ e)
    (hnece : c ≠ e) : False := by
  have hnca : ¬ coverAdj X Y c a := by
    intro h
    exact hnac (coverAdj_flip X Y c a h)
  have hnda : ¬ coverAdj X Y d a := by
    intro h
    exact hnad (coverAdj_flip X Y d a h)
  have hndb : ¬ coverAdj X Y d b := by
    intro h
    exact hnbd (coverAdj_flip X Y d b h)
  have hneb : ¬ coverAdj X Y e b := by
    intro h
    exact hnbe (coverAdj_flip X Y e b h)
  have hnec : ¬ coverAdj X Y e c := by
    intro h
    exact hnce (coverAdj_flip X Y e c h)
  have habSides : a.1 ≠ b.1 :=
    cover_induced_cycle_edge_crosses_sides
      X Y a b c e hab hbc hea hnac hnbe hnce
      hneac hnebe hnece
  have hbcSides : b.1 ≠ c.1 :=
    cover_induced_cycle_edge_crosses_sides
      X Y b c d a hbc hcd hab hnbd hnca hnda
      hnebd hneac.symm hnead.symm
  have hcdSides : c.1 ≠ d.1 :=
    cover_induced_cycle_edge_crosses_sides
      X Y c d e b hcd hde hbc hnce hndb hneb
      hnece hnebd.symm hnebe.symm
  have hdeSides : d.1 ≠ e.1 :=
    cover_induced_cycle_edge_crosses_sides
      X Y d e a c hde hea hcd hnda hnec hnac
      hnead.symm hnece.symm hneac
  have heaSides : e.1 ≠ a.1 :=
    cover_induced_cycle_edge_crosses_sides
      X Y e a b d hea hab hde hneb hnad hnbd
      hnebe.symm hnead hnebd
  cases ha : a.1 <;> cases hb : b.1 <;>
    cases hc : c.1 <;> cases hd : d.1 <;>
    cases he : e.1 <;> simp_all

end EPPAIII.CliqueCovers
