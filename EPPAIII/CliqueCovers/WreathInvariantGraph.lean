import EPPAIII.CliqueCovers.WreathPairOrbits

/-!
# Every wreath-invariant graph has only two adjacency parameters

Once the outside vertices are identified with a natural s-by-t
profile parameter space, their induced graph is invariant under
all independent within-clique and outer index permutations.

This theorem proves that such invariance allows exactly two adjacency
parameters: one for pairs in the same coordinate clique and one for
pairs in different cliques. It is the finite pair-orbit portion of
the one-partial-case argument in Lemma 3.7.

The final use of the equal-edge-count identity to select the
sK_t pattern remains a separate arithmetic/graph-counting step.
-/

namespace EPPAIII.CliqueCovers

/-- The two uniform adjacency values are witnessed by concrete
ordered pairs, provided s,t are at least two. -/
theorem wreath_invariant_graph_two_parameters {s t : ℕ}
    (B : SimpleGraph (Fin s × Fin t))
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hInvariant : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      IsGraphAutomorphism B
        ((outerPermutation outer).trans (innerPermutation inner))) :
    ∃ (within between : Prop),
      (∀ x y : Fin s × Fin t, x ≠ y → x.1 = y.1 →
        (B.Adj x y ↔ within)) ∧
      (∀ x y : Fin s × Fin t, x.1 ≠ y.1 →
        (B.Adj x y ↔ between)) := by
  let i0 : Fin s := ⟨0, by omega⟩
  let i1 : Fin s := ⟨1, by omega⟩
  let a0 : Fin t := ⟨0, by omega⟩
  let a1 : Fin t := ⟨1, by omega⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [i0,i1] at hv
  have ha01 : a0 ≠ a1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [a0,a1] at hv
  have hWithinDistinct : (i0,a0) ≠ (i0,a1) := by
    intro h
    exact ha01 (congrArg Prod.snd h)
  have hBetweenDistinct : (i0,a0) ≠ (i1,a0) := by
    intro h
    exact hi01 (congrArg Prod.fst h)
  refine ⟨B.Adj (i0,a0) (i0,a1),
    B.Adj (i0,a0) (i1,a0), ?_, ?_⟩
  · intro x y hxy hSame
    apply wreath_invariant_graph_pair_uniform B hInvariant
      x y (i0,a0) (i0,a1) hxy hWithinDistinct
    exact ⟨fun _ => rfl, fun _ => hSame⟩
  · intro x y hCross
    have hDifferent : (x.1 = y.1) ↔ (i0 = i1) := by
      constructor
      · intro h
        exact False.elim (hCross h)
      · intro h
        exact False.elim (hi01 h)
    exact wreath_invariant_graph_pair_uniform B hInvariant
      x y (i0,a0) (i1,a0)
      (by
        intro h
        exact hCross (congrArg Prod.fst h))
      hBetweenDistinct hDifferent

/-- All adjacency in a wreath-invariant graph is determined by
two predicates, with the diagonal explicitly excluded. -/
theorem wreath_invariant_graph_adj_characterization {s t : ℕ}
    (B : SimpleGraph (Fin s × Fin t))
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hInvariant : ∀ (outer : Equiv.Perm (Fin s))
      (inner : Fin s → Equiv.Perm (Fin t)),
      IsGraphAutomorphism B
        ((outerPermutation outer).trans (innerPermutation inner))) :
    ∃ (within between : Prop),
      ∀ x y : Fin s × Fin t,
        (B.Adj x y ↔
          x ≠ y ∧ if x.1 = y.1 then within else between) := by
  obtain ⟨within,between,hWithin,hBetween⟩ :=
    wreath_invariant_graph_two_parameters B hs ht hInvariant
  refine ⟨within,between,?_⟩
  intro x y
  constructor
  · intro hAdj
    have hne : x ≠ y := B.ne_of_adj hAdj
    refine ⟨hne, ?_⟩
    by_cases hh : x.1 = y.1
    · simpa [hh] using (hWithin x y hne hh).mp hAdj
    · simpa [hh] using (hBetween x y hh).mp hAdj
  · rintro ⟨hne,hValue⟩
    by_cases hh : x.1 = y.1
    · exact (hWithin x y hne hh).mpr (by simpa [hh] using hValue)
    · exact (hBetween x y hh).mpr (by simpa [hh] using hValue)

end EPPAIII.CliqueCovers
