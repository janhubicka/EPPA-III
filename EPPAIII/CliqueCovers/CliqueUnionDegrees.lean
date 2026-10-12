import EPPAIII.CliqueCovers.Basic
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# Regular degrees of the two canonical clique-block graph patterns

The natural S_t wr S_s action has two basic nontrivial invariant
graphs on Fin s × Fin t: the disjoint union sK_t and its complement,
the complete s-partite graph with equal parts of order t.

Their degrees are t-1 and (s-1)*t respectively, and for s,t≥2
the second exceeds the first. The complete graph has degree st-1
and the empty graph degree zero. These degree comparisons, together
with the equal-edge-count regular graph lemma, will select sK_t
among the four invariant possibilities in Lemma 3.7.
-/

namespace EPPAIII.CliqueCovers

/-- A disjoint union of s copies of K_t is the complement of
Mathlib's complete equipartite graph K_s(t). -/
theorem cliqueUnion_eq_compl_completeEquipartite (s t : ℕ) :
    cliqueUnion s t = (SimpleGraph.completeEquipartiteGraph s t)ᶜ := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  by_cases hij : i = j
  · subst j
    simp [SimpleGraph.compl_adj, cliqueUnion,
      SimpleGraph.completeEquipartiteGraph_adj]
  · simp [SimpleGraph.compl_adj, cliqueUnion,
      SimpleGraph.completeEquipartiteGraph_adj, hij]

/-- Every vertex of the disjoint-clique graph has degree t-1. -/
theorem cliqueUnion_degree {s t : ℕ} [DecidableRel (cliqueUnion s t).Adj]
    (hs : 0 < s) (v : Fin s × Fin t) :
    (cliqueUnion s t).degree v = t - 1 := by
  classical
  have hN :
      (cliqueUnion s t).neighborFinset v =
        ({v.1} : Finset (Fin s)) ×ˢ
          ((Finset.univ : Finset (Fin t)).erase v.2) := by
    ext z
    rcases z with ⟨j,b⟩
    simp only [SimpleGraph.mem_neighborFinset,
      Finset.mem_product, Finset.mem_singleton,
      Finset.mem_erase, Finset.mem_univ, and_true]
    change (v.1 = j ∧ v.2 ≠ b) ↔ (j = v.1 ∧ b ≠ v.2)
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h => ⟨h.1.symm, h.2.symm⟩⟩
  calc
    (cliqueUnion s t).degree v =
        ((cliqueUnion s t).neighborFinset v).card := rfl
    _ = ({v.1} : Finset (Fin s)).card *
        ((Finset.univ : Finset (Fin t)).erase v.2).card := by
      rw [hN, Finset.card_product]
    _ = t - 1 := by simp

/-- The canonical sK_t graph is regular. -/
theorem cliqueUnion_regular {s t : ℕ} [DecidableRel (cliqueUnion s t).Adj]
    (hs : 0 < s) :
    (cliqueUnion s t).IsRegularOfDegree (t - 1) := by
  classical
  intro v
  exact cliqueUnion_degree hs v

/-- The complementary complete multipartite graph is regular
of degree (s-1)t. -/
theorem cliqueUnion_compl_regular {s t : ℕ}
    [DecidableRel ((cliqueUnion s t)ᶜ).Adj] :
    (cliqueUnion s t)ᶜ.IsRegularOfDegree ((s - 1) * t) := by
  classical
  intro v
  have hN :
      ((cliqueUnion s t)ᶜ).neighborFinset v =
        ({v.1}ᶜ : Finset (Fin s)) ×ˢ
          (Finset.univ : Finset (Fin t)) := by
    ext z
    rcases z with ⟨j,b⟩
    by_cases hij : v.1 = j
    · simp [SimpleGraph.mem_neighborFinset,
        SimpleGraph.compl_adj, cliqueUnion,
        Finset.mem_product, hij]
    · simp [SimpleGraph.mem_neighborFinset,
        SimpleGraph.compl_adj, cliqueUnion,
        Finset.mem_product, hij]
  calc
    ((cliqueUnion s t)ᶜ).degree v =
        (((cliqueUnion s t)ᶜ).neighborFinset v).card := rfl
    _ = ({v.1}ᶜ : Finset (Fin s)).card *
        (Finset.univ : Finset (Fin t)).card := by
      rw [hN, Finset.card_product]
    _ = (s - 1) * t := by simp [Finset.card_compl]

/-- The four invariant graph patterns have pairwise distinguishable
degrees at the degree t-1 of sK_t when s,t≥2. -/
theorem cliqueUnion_degree_distinct_of_nontrivial
    (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    0 < t - 1 ∧ t - 1 < (s - 1) * t ∧
      t - 1 < s * t - 1 := by
  have hFirst : t ≤ (s - 1) * t := by
    calc
      t = 1 * t := by simp
      _ ≤ (s - 1) * t :=
        Nat.mul_le_mul_right t (by omega)
  have hSecond : 2 * t ≤ s * t :=
    Nat.mul_le_mul_right t hs
  omega

end EPPAIII.CliqueCovers
