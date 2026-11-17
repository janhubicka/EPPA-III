import EPPAIII.BlockSystems.GardinerLiteralNormalization
import EPPAIII.TwoGraphs.PairParity
import EPPAIII.TwoGraphs.TwoGraphDescendant
import Mathlib.Data.Fintype.Option

/-! # The nontrivial homogeneous two-graph orders from Gardiner -/

namespace EPPAIII.TwoGraphs

open EPPAIII.BlockSystems EPPAIII.CliqueCovers EPPAIII.DoubleCover

private theorem cluster_of_clique_model {A : Type*} {G : SimpleGraph A} {s t : ℕ}
    (φ : (Fin s × Fin t) ≃ A) (hModel : CanonicalBaseCopy (cliqueUnion s t) G φ) :
    IsClusterGraph G := by
  intro a b c hab hbc hac
  have hAB : (cliqueUnion s t).Adj (φ.symm a) (φ.symm b) :=
    (hModel _ _).mpr (by simpa using hab)
  have hBC : (cliqueUnion s t).Adj (φ.symm b) (φ.symm c) :=
    (hModel _ _).mpr (by simpa using hbc)
  have hIndex := hAB.1.trans hBC.1
  have hAC : (cliqueUnion s t).Adj (φ.symm a) (φ.symm c) :=
    ⟨hIndex, fun h => hac (φ.symm.injective (Prod.ext hIndex h))⟩
  simpa using (hModel _ _).mp hAC

private theorem cocluster_of_clique_model {A : Type*} {G : SimpleGraph A} {s t : ℕ}
    (φ : (Fin s × Fin t) ≃ A) (hModel : CanonicalBaseCopy (cliqueUnion s t)ᶜ G φ) :
    IsCoClusterGraph G := by
  have hCompl : CanonicalBaseCopy (cliqueUnion s t) Gᶜ φ := by
    intro x y
    have h := hModel x y
    by_cases hxy : x = y
    · subst y
      simp
    · change (x ≠ y ∧ ¬ (cliqueUnion s t).Adj x y) ↔ G.Adj (φ x) (φ y) at h
      change (cliqueUnion s t).Adj x y ↔ φ x ≠ φ y ∧ ¬ G.Adj (φ x) (φ y)
      simpa [hxy, φ.injective.ne hxy] using not_congr h
  have hCluster := cluster_of_clique_model φ hCompl
  intro a b c hab hbc hac hnAB hnBC
  exact (hCluster a b c ⟨hab, hnAB⟩ ⟨hbc, hnBC⟩ hac).2

universe u

/-- Each rooted descendant of a nontrivial finite homogeneous two-graph
is a pentagon or the three-by-three rook graph, by Gardiner's theorem. -/
theorem homogeneous_two_graph_nontrivial_descendant_of_gardiner
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGardiner : ∀ {A : Type u} [Fintype A] (H : SimpleGraph A),
      Nonempty A → IsHomogeneousGraph H → GardinerPublishedModels H)
    (hHom : IsHomogeneousTwoGraph G)
    (hOdd : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ OddBaseTriple G a b c)
    (hEven : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple G a b c)
    (r : V) :
    Nonempty (SimpleGraph.cycleGraph 5 ≃g rootDescendant G r) ∨
      Nonempty (rookThreeGraph ≃g rootDescendant G r) := by
  classical
  have hOther : Nonempty {v : V // v ≠ r} := by
    obtain ⟨a, b, _, hab, _, _, _⟩ := hOdd
    by_cases har : a = r
    · exact ⟨⟨b, fun hbr => hab (har.trans hbr.symm)⟩⟩
    · exact ⟨⟨a, har⟩⟩
  obtain ⟨x₀⟩ := hOther
  have hRoot := rootDescendant_homogeneous G hHom r
  have hPairs := two_graph_homogeneous_has_third_points G hHom hOdd hEven
  obtain hCluster | hCoCluster | ⟨φ, hφ⟩ | ⟨φ, hφ⟩ :=
    gardiner_published_implies_normalized (rootDescendant G r)
      (hGardiner (rootDescendant G r) ⟨x₀⟩ hRoot)
  · obtain ⟨s, t, _, _, φ, hφ⟩ := hCluster
    exact (rootDescendant_not_cluster G r x₀ hPairs (cluster_of_clique_model φ hφ)).elim
  · obtain ⟨s, t, _, _, φ, hφ⟩ := hCoCluster
    exact (rootDescendant_not_cocluster G r x₀ hPairs (cocluster_of_clique_model φ hφ)).elim
  · exact Or.inl ⟨⟨φ, fun {a b} => (hφ a b).symm⟩⟩
  · exact Or.inr ⟨⟨φ, fun {a b} => (hφ a b).symm⟩⟩

/-- The nontrivial homogeneous two-graphs have six or ten points. -/
theorem homogeneous_two_graph_nontrivial_order_of_gardiner
    {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGardiner : ∀ {A : Type u} [Fintype A] (H : SimpleGraph A),
      Nonempty A → IsHomogeneousGraph H → GardinerPublishedModels H)
    (hHom : IsHomogeneousTwoGraph G)
    (hOdd : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ OddBaseTriple G a b c)
    (hEven : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple G a b c) :
    Fintype.card V = 6 ∨ Fintype.card V = 10 := by
  classical
  obtain ⟨r, x, y, hrx, hry, hxy, hOddTriple⟩ := hOdd
  have hCard : Fintype.card {v : V // v ≠ r} + 1 = Fintype.card V := by
    simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe r)
  obtain hCycle | hRook := homogeneous_two_graph_nontrivial_descendant_of_gardiner G
    (fun H => hGardiner H) hHom ⟨r, x, y, hrx, hry, hxy, hOddTriple⟩ hEven r
  · obtain ⟨φ⟩ := hCycle
    have h := Fintype.card_congr φ.toEquiv
    simp at h
    omega
  · obtain ⟨φ⟩ := hRook
    have h := Fintype.card_congr φ.toEquiv
    simp at h
    omega

end EPPAIII.TwoGraphs
