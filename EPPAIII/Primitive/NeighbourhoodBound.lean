import EPPAIII.EPPA.PartialSwap
import Mathlib.Data.Fintype.BigOperators

/-!
# Bounding an EPPA base by the size of a stabilizer base

Pointwise fixation of the chosen anchors and EPPA make the neighbourhood
profiles of the remaining vertices distinct.
-/

namespace EPPAIII.Primitive

/-- A graph automorphism can send one selected vertex to a second while
fixing all selected anchors whenever the two vertices have the same
adjacency profile into the anchors. -/
theorem eppa_same_profile_extension {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (U : Finset V) (a b : V)
    (ha : a ∉ U) (hb : b ∉ U)
    (hEqual : ∀ u ∈ U, G.Adj a u ↔ G.Adj b u) :
    ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q (e a) = e b ∧
      (∀ u ∈ U, q (e u) = e u) := by
  obtain ⟨q, hq, hExtend⟩ :=
    heppa.2 (insert a U) (Equiv.swap a b)
      (equal_types_partial_swap G U a b ha hb hEqual)
  refine ⟨q, hq, ?_, ?_⟩
  · simpa using hExtend a (Finset.mem_insert_self a U)
  · intro u hu
    have hua : u ≠ a := fun h => ha (h ▸ hu)
    have hub : u ≠ b := fun h => hb (h ▸ hu)
    simpa only [Equiv.swap_apply_of_ne_of_ne hua hub] using
      hExtend u (Finset.mem_insert_of_mem hu)

/-- A set of anchors with trivial pointwise stabilizer gives the
neighbourhood bound of Section 7. It is enough that the stabilizer
acts trivially on the selected copy. -/
theorem card_le_pow_add_of_pointwise_fixation {V W : Type*}
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) (U : Finset V)
    (hFix : ∀ q : Equiv.Perm W, IsGraphAutomorphism H q →
      (∀ u ∈ U, q (e u) = e u) → ∀ v, q (e v) = e v) :
    Fintype.card V ≤ 2 ^ U.card + U.card := by
  classical
  let profile : (↥Uᶜ : Type _) → (↥U → Bool) :=
    fun v u => decide (G.Adj v u)
  have hInjective : Function.Injective profile := by
    intro a b h
    apply Subtype.ext
    have ha : (a : V) ∉ U := Finset.mem_compl.mp a.property
    have hb : (b : V) ∉ U := Finset.mem_compl.mp b.property
    obtain ⟨q, hq, hMap, hAnchors⟩ :=
      eppa_same_profile_extension G H e heppa U a b ha hb (by
        intro u hu
        have hAt := congrFun h (⟨u, hu⟩ : ↥U)
        change decide (G.Adj a u) = decide (G.Adj b u) at hAt
        exact decide_eq_decide.mp hAt)
    exact e.injective ((hFix q hq hAnchors a).symm.trans hMap)
  have hCard := Fintype.card_le_of_injective profile hInjective
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, Fintype.card_coe] at hCard
  have hSplit := Finset.card_compl_add_card U
  omega

end EPPAIII.Primitive
