import EPPAIII.Primitive.AlternatingFiveExclusion
import EPPAIII.Primitive.NonlocalConnectivity
import EPPAIII.Primitive.OrthogonalEightConstituents
import EPPAIII.Primitive.SRGIndependentBound
import Mathlib.Tactic.Linarith

/-! # Conway's graph on 1408 vertices -/

namespace EPPAIII.Primitive

open SimpleGraph

private def conway1408Parameters : SRGParameters := ⟨1408, 567, 246, 216⟩

/-- The parameters alone bound independent sets in Conway's graph well below
the size required by a complementary cover in the second constituent. -/
theorem conway1408_independent_size_le {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 1408 567 246 216)
    {m : ℕ} (f : Fin m ↪ V) (hf : ∀ i j, ¬ H.Adj (f i) (f j)) : m ≤ 28 := by
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · decide
  have hCS := srg_independent_size_bound H h f hf
  have hLinear : m * (17361 * m) ≤ m * 494208 := by
    zify [show 1 ≤ m by omega] at hCS ⊢
    nlinarith only [hCS]
  have hBound := Nat.le_of_mul_le_mul_left hLinear hm
  omega

/-- The actual local and nonlocal constituents of an SRG with the Conway
1408 parameters each fail all four of the reduced Section 8 forms.
No model identification or stabilizer assumption is needed once the SRG
parameters are supplied. -/
theorem conway1408_constituents_exclude_forms {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 1408 567 246 216) (root : V) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
    ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  classical
  let J := localGraph H root
  let K := nonlocalGraph H root
  have hLocal := constituentGraph_profile H conway1408Parameters h root false
  have hLocalOrder : Fintype.card (H.neighborSet root) = 567 :=
    Nat.card_eq_fintype_card.symm.trans hLocal.1
  have hLocalRegular : J.IsRegularOfDegree 246 := by
    intro x
    rw [← J.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hLocal.2 x
  have hNonlocal := constituentGraph_profile H conway1408Parameters h root true
  have hNonlocalOrder : Fintype.card {x : V // root ≠ x ∧ ¬ H.Adj root x} = 840 :=
    Nat.card_eq_fintype_card.symm.trans hNonlocal.1
  have hNonlocalRegular : K.IsRegularOfDegree 351 := by
    intro x
    rw [← K.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hNonlocal.2 x
  have hConnected : K.Connected := by
    apply nonlocalGraph_connected_of_degree_lt_order H h (by decide) root
    rw [Nat.card_eq_fintype_card, hNonlocalOrder]
    decide
  constructor
  · have hLocalExcluded := sparse_regular_constituent_excludes_forms J hLocalRegular
      (by decide) (by rw [hLocalOrder]; decide)
      (Or.inl (by rw [hLocalOrder]))
      (by rw [hLocalOrder]; decide) (by rw [hLocalOrder]; decide) (by rw [hLocalOrder]; decide)
    rintro (⟨s, t, hModel⟩ | ⟨s, t, X, Y, hModel⟩)
    · rcases hModel with hIso | hCompl
      · obtain ⟨φ⟩ := hIso
        exact (hLocalExcluded.1 s t).false φ
      · obtain ⟨φ⟩ := hCompl
        exact (hLocalExcluded.2.1 s t).false φ
    · rcases hModel with hIso | hCompl
      · obtain ⟨φ⟩ := hIso
        exact (hLocalExcluded.2.2.1 s t X Y).false φ
      · obtain ⟨φ⟩ := hCompl
        exact (hLocalExcluded.2.2.2 s t X Y).false φ
  · have hSparse : 2 * 351 + 2 < Fintype.card {x : V // root ≠ x ∧ ¬ H.Adj root x} := by
      rw [hNonlocalOrder]
      decide
    rintro (⟨s, t, hModel⟩ | ⟨s, t, X, Y, hModel⟩)
    · exact sparseConnected_not_cliqueUnion_or_compl K hConnected hNonlocalRegular
        (by decide) hSparse hModel
    · rcases hModel with hIso | hCompl
      · obtain ⟨φ⟩ := hIso
        exact sparseConnected_not_cover K hConnected hNonlocalRegular hSparse X Y φ
      · obtain ⟨φ⟩ := hCompl
        have hGap : 2 * (351 + 28) < Fintype.card {x : V // root ≠ x ∧ ¬ H.Adj root x} := by
          rw [hNonlocalOrder]
          decide
        refine not_compl_cover_of_independence_gap K hNonlocalRegular ?_ hGap X Y φ
        intro m f hf
        exact conway1408_independent_size_le H h (f.trans (Function.Embedding.subtype _)) hf

end EPPAIII.Primitive
