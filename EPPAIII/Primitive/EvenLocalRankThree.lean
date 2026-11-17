import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.RankThree

/-!
# The even-even alternative for subconstituents

Even subconstituent orders give odd host order. At least half then means a
strict majority in the host, so rank three follows before the small-witness
reduction is applied a second time to any strict-majority subconstituent.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers (HasTransitiveGraphAutomorphisms)

private theorem strict_maxEppaOrder_clique_empty_or_rank_three {V : Type*} [Finite V]
    (H : SimpleGraph V) (hTrans : HasTransitiveGraphAutomorphisms H)
    (hStrict : Nat.card V < 2 * maxEppaOrder H) :
    H = ⊤ ∨ H = ⊥ ∨ HasRankThreeAutAction H := by
  classical
  letI := Fintype.ofFinite V
  obtain ⟨S, hOrder, hEppa⟩ := maxEppaOrder_attained H
  letI := Fintype.ofFinite S
  have hStrict' : Fintype.card V < 2 * Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hOrder]
    exact hStrict
  exact transitive_eppa_at_most_double_clique_empty_or_rank_three
    (H.induce S) H _ hEppa hTrans hStrict'.le (fun h => (hStrict'.ne h).elim)

theorem localGraph_transitive {V : Type*} (H : SimpleGraph V)
    (hRank : HasRankThreeAutAction H) (root : V) :
    HasTransitiveGraphAutomorphisms (localGraph H root) := by
  have hSet : H.neighborSet root = {x | root ≠ x ∧ (H.Adj root x ↔ True)} := by
    ext x
    simp only [SimpleGraph.mem_neighborSet, Set.mem_ofPred_eq, iff_true]
    exact ⟨fun h => ⟨H.ne_of_adj h, h⟩, And.right⟩
  unfold localGraph
  rw [hSet]
  exact rankThree_pointwise_transitive H hRank root True

theorem nonlocalGraph_transitive {V : Type*} (H : SimpleGraph V)
    (hRank : HasRankThreeAutAction H) (root : V) :
    HasTransitiveGraphAutomorphisms (nonlocalGraph H root) := by
  have hSet : {x | root ≠ x ∧ ¬ H.Adj root x} =
      {x | root ≠ x ∧ (H.Adj root x ↔ False)} := by
    ext x
    exact and_congr Iff.rfl ⟨fun h => ⟨h, False.elim⟩, Iff.mp⟩
  unfold nonlocalGraph
  rw [hSet]
  exact rankThree_pointwise_transitive H hRank root False

private theorem induce_top {V : Type*} (S : Set V) :
    (⊤ : SimpleGraph V).induce S = ⊤ := by
  ext x y
  change (x : V) ≠ (y : V) ↔ x ≠ y
  exact ⟨fun h hEq => h (congrArg Subtype.val hEq),
    fun h hEq => h (Subtype.ext hEq)⟩

private theorem induce_bot {V : Type*} (S : Set V) :
    (⊥ : SimpleGraph V).induce S = ⊥ := by
  ext x y
  rfl

/-- Proposition local, with the EPPA hypothesis on the final even-even
alternative made explicit. `hHalf` asserts that the host lies in the
manuscript's class of witnesses for at least half their order. -/
theorem even_subconstituents_rank_three_or_equal {V : Type*} [Finite V]
    (H : SimpleGraph V) (root : V)
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (hHalf : Nat.card V ≤ 2 * maxEppaOrder H)
    (hEvenL : Even (Nat.card (H.neighborSet root)))
    (hEvenN : Even (Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x})) :
    (Nat.card (H.neighborSet root) < 2 * maxEppaOrder (localGraph H root) ∧
      (localGraph H root = ⊤ ∨ localGraph H root = ⊥ ∨
        HasRankThreeAutAction (localGraph H root))) ∨
    (Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x} <
      2 * maxEppaOrder (nonlocalGraph H root) ∧
      (nonlocalGraph H root = ⊤ ∨ nonlocalGraph H root = ⊥ ∨
        HasRankThreeAutAction (nonlocalGraph H root))) ∨
    (2 * maxEppaOrder (localGraph H root) = Nat.card (H.neighborSet root) ∧
      2 * maxEppaOrder (nonlocalGraph H root) =
        Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x}) := by
  have hSplit := order_eq_one_add_subconstituent_orders H root
  have hOdd : Nat.card V % 2 = 1 := by
    obtain ⟨a, ha⟩ := hEvenL
    obtain ⟨b, hb⟩ := hEvenN
    omega
  have hStrict : Nat.card V < 2 * maxEppaOrder H := by omega
  have hHost := strict_maxEppaOrder_clique_empty_or_rank_three H hTrans hStrict
  rcases even_subconstituent_orders_strict_or_equal H root hTrans hHalf hEvenL hEvenN with
    hLocal | hNonlocal | hEq
  · left
    refine ⟨hLocal, ?_⟩
    rcases hHost with hTop | hBot | hRank
    · left
      simp only [localGraph, hTop, induce_top]
    · right; left
      simp only [localGraph, hBot, induce_bot]
    · exact strict_maxEppaOrder_clique_empty_or_rank_three
        (localGraph H root) (localGraph_transitive H hRank root) hLocal
  · right; left
    refine ⟨hNonlocal, ?_⟩
    rcases hHost with hTop | hBot | hRank
    · left
      simp only [nonlocalGraph, hTop, induce_top]
    · right; left
      simp only [nonlocalGraph, hBot, induce_bot]
    · exact strict_maxEppaOrder_clique_empty_or_rank_three
        (nonlocalGraph H root) (nonlocalGraph_transitive H hRank root) hNonlocal
  · exact Or.inr (Or.inr hEq)

end EPPAIII.Primitive
