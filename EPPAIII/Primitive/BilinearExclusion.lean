import EPPAIII.Primitive.BilinearConstituentObstructions
import EPPAIII.Primitive.GrassmannRookObstruction
import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.RankThreeCases

/-! # The bilinear forms branch of the primitive reduction -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem not_cliqueUnionOrCover_of_rookThree {V : Type*} {G : SimpleGraph V}
    (f : rookGraph 3 ↪g G) : ¬ HasCliqueUnionOrCoverModel G := by
  rintro (⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩)
  · rcases h with h | h
    · obtain ⟨φ⟩ := h
      exact (no_clique_union_or_compl_of_induced_rookThree f s t).1.false φ
    · obtain ⟨φ⟩ := h
      exact (no_clique_union_or_compl_of_induced_rookThree f s t).2.false φ
  · rcases h with h | h
    · obtain ⟨φ⟩ := h
      exact (no_cover_or_compl_of_induced_rookThree f s t X Y).1.false φ
    · obtain ⟨φ⟩ := h
      exact (no_cover_or_compl_of_induced_rookThree f s t X Y).2.false φ

private def bilinearTranslation {F : Type*} [Field F] {m : ℕ}
    (r : Matrix (Fin 2) (Fin m) F) : bilinearFormsGraph F m ≃g bilinearFormsGraph F m where
  toEquiv := Equiv.subRight r
  map_rel_iff' := by
    intro A B
    change ((A - r) - (B - r)).rank = 1 ↔ (A - B).rank = 1
    rw [sub_sub_sub_cancel_right]

private def bilinearLocalIsoZero {F : Type*} [Field F] {m : ℕ} :
    localGraph (bilinearFormsGraph F m) 0 ≃g bilinearFormsRankOneGraph F m where
  toEquiv := (Equiv.refl _).subtypeEquiv bilinearFormsGraph_zero_adj_iff
  map_rel_iff' := Iff.rfl

private def bilinearNonlocalIsoZero {F : Type*} [Field F] {m : ℕ} :
    nonlocalGraph (bilinearFormsGraph F m) 0 ≃g bilinearFormsRankTwoGraph F m where
  toEquiv := (Equiv.refl _).subtypeEquiv fun A =>
    (and_congr (ne_comm (a := 0) (b := A)) Iff.rfl).trans (bilinearFormsGraph_zero_nonadj_iff A)
  map_rel_iff' := Iff.rfl

private def bilinearLocalIso {F : Type*} [Field F] {m : ℕ}
    (r : Matrix (Fin 2) (Fin m) F) :
    localGraph (bilinearFormsGraph F m) r ≃g bilinearFormsRankOneGraph F m := by
  have h := localIso (bilinearTranslation r) r
  change localGraph (bilinearFormsGraph F m) r ≃g localGraph (bilinearFormsGraph F m) (r - r) at h
  have ψ : localGraph (bilinearFormsGraph F m) r ≃g localGraph (bilinearFormsGraph F m) 0 :=
    Eq.ndrec (motive := fun z =>
      localGraph (bilinearFormsGraph F m) r ≃g localGraph (bilinearFormsGraph F m) z) h (sub_self r)
  exact ψ.trans bilinearLocalIsoZero

private def bilinearNonlocalIso {F : Type*} [Field F] {m : ℕ}
    (r : Matrix (Fin 2) (Fin m) F) :
    nonlocalGraph (bilinearFormsGraph F m) r ≃g bilinearFormsRankTwoGraph F m := by
  have h := nonlocalIso (bilinearTranslation r) r
  change nonlocalGraph (bilinearFormsGraph F m) r ≃g
    nonlocalGraph (bilinearFormsGraph F m) (r - r) at h
  have ψ : nonlocalGraph (bilinearFormsGraph F m) r ≃g nonlocalGraph (bilinearFormsGraph F m) 0 :=
    Eq.ndrec (motive := fun z =>
      nonlocalGraph (bilinearFormsGraph F m) r ≃g nonlocalGraph (bilinearFormsGraph F m) z) h (sub_self r)
  exact ψ.trans bilinearNonlocalIsoZero

/-- In either orientation of the bilinear forms graph, neither constituent
at any root has one of the four Section 8 forms. -/
theorem bilinearForms_model_excludes_forms {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m)
    {W : Type*} {H : SimpleGraph W} (root : W)
    (hModel : IsModelUpToComplement H (bilinearFormsGraph F m)) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  apply constituent_forms_exclusion_of_model _ hModel root
  intro r
  have f := (SimpleGraph.Iso.toEmbedding (bilinearLocalIso r).symm).comp
    (bilinearRankOne_rookThree (F := F) hm)
  have g := (SimpleGraph.Iso.toEmbedding (bilinearNonlocalIso r).symm).comp
    (bilinearRankTwo_fiveCycle (F := F) hm)
  exact ⟨not_cliqueUnionOrCover_of_rookThree f, not_cliqueUnionOrCover_of_fiveCycle g⟩

/-- An actual half-order selection in a vertex-transitive bilinear forms model
contradicts the Section 8 shape claim at its selected root. -/
theorem bilinearForms_no_halfOrder_eppa_of_constituent_shapes
    {F : Type*} [Field F] {m : ℕ} (hm : 3 ≤ m)
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (root : V)
    (hModel : IsModelUpToComplement H (bilinearFormsGraph F m))
    (hLocalShape : Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      HasCliqueUnionOrCoverModel (localGraph H (e root)))
    (hNonlocalShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root))) : False := by
  obtain ⟨hLocal, hNonlocal⟩ := bilinearForms_model_excludes_forms hm (e root) hModel
  exact (selected_subconstituent_at_least_half G H e root hTrans hHalf).elim
    (fun h => hLocal (hLocalShape h)) (fun h => hNonlocal (hNonlocalShape h))

end EPPAIII.Primitive
