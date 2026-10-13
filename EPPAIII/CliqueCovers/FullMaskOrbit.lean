import EPPAIII.CliqueCovers.FullCoordinateArithmetic
import EPPAIII.CliqueCovers.WreathChoiceTransitivity

/-!
# Full-coordinate masks under the clique-index permutation group

In the no-partial-neighbourhood branch, an outside true-twin clique
is adjacent completely to an index set S of the distinguished K_t
components and not at all to the others.

Every permutation of the s base clique indices lifts by EPPA. Thus
the masks in the orbit of S must occur as masks of outside twin
classes. Here we prove the exact orbit cardinality choose(s,|S|),
and the arithmetic consequence of an upper bound of s masks:
|S| is 0,1,s−1, or s.

The group-action realization of these masks by actual outside twin
classes remains an additional graph-level obligation, not assumed
by the present combinatorial theorem.
-/

namespace EPPAIII.CliqueCovers

/-- All images of an index mask under permutations of the s
distinguished clique indices. -/
noncomputable def outerMaskOrbit {s : ℕ}
    (S : Finset (Fin s)) : Finset (Finset (Fin s)) := by
  classical
  exact (Finset.univ : Finset (Equiv.Perm (Fin s))).image
    (fun p => S.map p.toEmbedding)

/-- Every r-subset of the index set occurs, where r = |S|. -/
theorem outerMaskOrbit_eq_powersetCard {s : ℕ}
    (S : Finset (Fin s)) :
    outerMaskOrbit S =
      (Finset.univ : Finset (Fin s)).powersetCard S.card := by
  classical
  ext R
  constructor
  · intro h
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, by simp⟩
  · intro h
    have hCard : S.card = R.card :=
      (Finset.mem_powersetCard.mp h).2.symm
    obtain ⟨p,hp⟩ := Equiv.Perm.exists_map_finset_eq S R hCard
    unfold outerMaskOrbit
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, hp⟩

/-- The orbit of a selected index mask has precisely choose(s,|S|)
members, with no assumption on the mask size. -/
theorem outerMaskOrbit_card {s : ℕ} (S : Finset (Fin s)) :
    (outerMaskOrbit S).card = Nat.choose s S.card := by
  classical
  rw [outerMaskOrbit_eq_powersetCard]
  simp [Finset.card_powersetCard]

/-- If at most s different full-coordinate masks occur,
their common number of selected base cliques is 0,1,s−1 or s. -/
theorem outerMaskOrbit_size_extreme {s : ℕ}
    (S : Finset (Fin s))
    (hBudget : (outerMaskOrbit S).card ≤ s) :
    S.card = 0 ∨ S.card = 1 ∨ S.card + 1 = s ∨
      S.card = s := by
  have hSize : S.card ≤ s := by
    simpa using (Finset.card_le_univ S)
  have hChoose : Nat.choose s S.card ≤ s := by
    rw [← outerMaskOrbit_card S]
    exact hBudget
  exact choose_le_row_index_extreme s S.card hSize hChoose

end EPPAIII.CliqueCovers
