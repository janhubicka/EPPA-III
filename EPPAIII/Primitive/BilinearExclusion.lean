import EPPAIII.BlockSystems.ImprimitiveGardinerBridge
import EPPAIII.Primitive.BilinearConstituentObstructions
import EPPAIII.Primitive.BilinearParity
import EPPAIII.Primitive.BilinearRankOne
import EPPAIII.Primitive.CoverHalfReduction
import EPPAIII.Primitive.OrthogonalEightConstituents
import EPPAIII.Primitive.PrimitiveCases
import Mathlib.Data.Fin.VecNotation

/-! # The bilinear forms branch of the primitive reduction -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.CliqueCovers EPPAIII.DoubleCover SimpleGraph

universe u

private instance : DecidableRel (pathGraph 4).Adj := fun _ _ =>
  decidable_of_iff _ pathGraph_adj.symm

private def pathFour_complEmbedding : pathGraph 4 ↪g (pathGraph 4)ᶜ where
  toFun := ![2, 0, 3, 1]
  inj' := by
    have h : ∀ i j : Fin 4, (![2, 0, 3, 1] : Fin 4 → Fin 4) i =
        (![2, 0, 3, 1] : Fin 4 → Fin 4) j → i = j := by decide
    exact fun {i j} => h i j
  map_rel_iff' := by
    let p : Fin 4 → Fin 4 := ![2, 0, 3, 1]
    have h : ∀ i j : Fin 4, (p i ≠ p j ∧ ¬ (pathGraph 4).Adj (p i) (p j)) ↔
        (pathGraph 4).Adj i j := by dsimp [p]; decide
    exact fun {i j} => h i j

private theorem no_induced_path_four_in_clique_union (s t : ℕ) :
    IsEmpty (pathGraph 4 ↪g cliqueUnion s t) := by
  refine ⟨fun f => ?_⟩
  have h01 : (cliqueUnion s t).Adj (f 0) (f 1) := f.map_adj_iff.mpr (by decide)
  have h12 : (cliqueUnion s t).Adj (f 1) (f 2) := f.map_adj_iff.mpr (by decide)
  have h02 : (f 0).1 = (f 2).1 := h01.1.trans h12.1
  have hCoord : (f 0).2 ≠ (f 2).2 :=
    fun h => (show (0 : Fin 4) ≠ 2 by decide) (f.injective (Prod.ext h02 h))
  exact (show ¬ (pathGraph 4).Adj 0 2 by decide) (f.map_adj_iff.mp ⟨h02, hCoord⟩)

private theorem no_induced_path_four_in_compl_clique_union (s t : ℕ) :
    IsEmpty (pathGraph 4 ↪g (cliqueUnion s t)ᶜ) := by
  refine ⟨fun f => (no_induced_path_four_in_clique_union s t).false ?_⟩
  have f' : (pathGraph 4)ᶜ ↪g cliqueUnion s t := by
    simpa only [compl_compl] using Embedding.complEquiv f
  exact f'.comp pathFour_complEmbedding

private theorem no_cliqueUnion_of_induced_path_four {S : Type*} {K : SimpleGraph S}
    (path : pathGraph 4 ↪g K) (s t : ℕ) : ¬ IsModelUpToComplement K (cliqueUnion s t) := by
  intro h
  rcases h with h | h
  · obtain ⟨φ⟩ := h
    exact (no_induced_path_four_in_clique_union s t).false (φ.toEmbedding.comp path)
  · obtain ⟨φ⟩ := h
    exact (no_induced_path_four_in_compl_clique_union s t).false (φ.toEmbedding.comp path)

private theorem nonhomogeneous_of_large_induced_path_four {S : Type*} [Fintype S]
    {K : SimpleGraph S} (path : pathGraph 4 ↪g K) (hOrder : 9 < Nat.card S)
    (hGardiner : IsHomogeneousGraph K → GardinerHomogeneousModels K) :
    ¬ IsHomogeneousGraph K := by
  intro hHom
  rcases hGardiner hHom with ⟨s, t, _, _, φ, hφ⟩ | ⟨s, t, _, _, φ, hφ⟩ |
    ⟨φ, _⟩ | ⟨φ, _⟩
  · exact no_cliqueUnion_of_induced_path_four path s t
      (Or.inl ⟨(show cliqueUnion s t ≃g K from ⟨φ, fun {x y} => (hφ x y).symm⟩).symm⟩)
  · exact no_cliqueUnion_of_induced_path_four path s t
      (Or.inr ⟨(show (cliqueUnion s t)ᶜ ≃g K from ⟨φ, fun {x y} => (hφ x y).symm⟩).symm⟩)
  · rw [← Nat.card_congr φ] at hOrder
    simpa [Nat.card_eq_fintype_card] using hOrder
  · rw [← Nat.card_congr φ] at hOrder
    simpa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod] using hOrder

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

private def bilinearLocalIso {F : Type*} [Field F] {m : ℕ} {W : Type*}
    {H : SimpleGraph W} (φ : H ≃g bilinearFormsGraph F m) (r : W) :
    localGraph H r ≃g bilinearFormsRankOneGraph F m := by
  have ψ : localGraph H r ≃g localGraph (bilinearFormsGraph F m) 0 := by
    have h := localIso (φ.trans (bilinearTranslation (φ r))) r
    change localGraph H r ≃g localGraph (bilinearFormsGraph F m) (φ r - φ r) at h
    exact Eq.ndrec (motive := fun z =>
      localGraph H r ≃g localGraph (bilinearFormsGraph F m) z) h (sub_self (φ r))
  exact ψ.trans bilinearLocalIsoZero

private def bilinearNonlocalIso {F : Type*} [Field F] {m : ℕ} {W : Type*}
    {H : SimpleGraph W} (φ : H ≃g bilinearFormsGraph F m) (r : W) :
    nonlocalGraph H r ≃g bilinearFormsRankTwoGraph F m := by
  have ψ : nonlocalGraph H r ≃g nonlocalGraph (bilinearFormsGraph F m) 0 := by
    have h := nonlocalIso (φ.trans (bilinearTranslation (φ r))) r
    change nonlocalGraph H r ≃g nonlocalGraph (bilinearFormsGraph F m) (φ r - φ r) at h
    exact Eq.ndrec (motive := fun z =>
      nonlocalGraph H r ≃g nonlocalGraph (bilinearFormsGraph F m) z) h (sub_self (φ r))
  exact ψ.trans bilinearNonlocalIsoZero

private theorem cover_bound_of_large_induced_path_four
    {S : Type u} {T : Type*} [Finite S] [Finite T] (J : SimpleGraph T) (K : SimpleGraph S)
    (e : T ↪ S) (hEppa : IsEPPAEmbedding J K e)
    (hTrans : HasTransitiveGraphAutomorphisms K)
    (path : pathGraph 4 ↪g K) (hOrder : 9 < Nat.card S)
    (hGardiner : ∀ {U : Type u} [Fintype U] (L : SimpleGraph U),
      IsHomogeneousGraph L → GardinerHomogeneousModels L)
    (hShape : HasCliqueUnionOrCoverModel K) : 2 * Nat.card T ≤ Nat.card S := by
  letI := Fintype.ofFinite S
  rcases hShape with ⟨s, t, hModel⟩ | ⟨s, t, X, Y, hCover⟩
  · exact False.elim (no_cliqueUnion_of_induced_path_four path s t hModel)
  · exact nonhomogeneous_cover_selected_at_most_half J K e hEppa hTrans
      (nonhomogeneous_of_large_induced_path_four path hOrder (hGardiner K)) X Y hCover

/-- For a rank-three bilinear forms host in either orientation, an actual EPPA
selection of at least half the host order contradicts the Section 8 model
constraint on every half-order constituent. Gardiner's classification is
supplied as an explicit normalized theorem input. -/
theorem bilinearForms_no_halfOrder_eppa_of_constituent_shapes
    {F : Type*} [Field F] [Fintype F] {m : ℕ} (hm : 3 ≤ m)
    {V : Type*} {W : Type u} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hEppa : IsEPPAEmbedding G H e) (hRank : HasRankThreeAutAction H)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) (root : V)
    (hModel : IsModelUpToComplement H (bilinearFormsGraph F m))
    (hGardiner : ∀ {S : Type u} [Fintype S] (K : SimpleGraph S),
      IsHomogeneousGraph K → GardinerHomogeneousModels K)
    (hLocalShape : Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      HasCliqueUnionOrCoverModel (localGraph H (e root)))
    (hNonlocalShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root))) : False := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hOrders := bilinear_constituent_order_parity hq hm
  have hRankOne : 9 < Nat.card (BilinearRankOne F m) := by
    rw [bilinearFormsRankOne_card]
    exact hOrders.1
  have hRankTwo : Even (Nat.card (BilinearRankTwo F m)) := by
    rw [bilinearFormsRankTwo_card (by omega : 2 ≤ m)]
    exact hOrders.2.2.2
  have path := bilinearRankOne_inducedPath (F := F) hm
  have cycle := bilinearRankTwo_fiveCycle (F := F) hm
  have hEither := selected_subconstituent_at_least_half G H e root hRank.2.2.1 hHalf
  have hSplitHost := order_eq_one_add_subconstituent_orders H (e root)
  have hSplitSelected := order_eq_one_add_subconstituent_orders G root
  rcases hModel with hModel | hModel
  · obtain ⟨φ⟩ := hModel
    let ψOne := bilinearLocalIso φ (e root)
    let ψTwo := bilinearNonlocalIso φ (e root)
    have hExclude := not_cliqueUnionOrCover_of_fiveCycle ((SimpleGraph.Iso.toEmbedding ψTwo.symm).comp cycle)
    rcases hEither with hLocal | hNonlocal
    · have hOrder := Nat.card_congr ψOne.toEquiv
      have hEven := Nat.card_congr ψTwo.toEquiv
      obtain ⟨n, hn⟩ := hRankTwo
      have hLocalBound := cover_bound_of_large_induced_path_four
        (localGraph G root) (localGraph H (e root)) _
        (local_eppa G H e hEppa root) (localGraph_transitive H hRank (e root))
        ((SimpleGraph.Iso.toEmbedding ψOne.symm).comp path) (by omega) hGardiner (hLocalShape hLocal)
      exact hExclude (hNonlocalShape (by omega))
    · exact hExclude (hNonlocalShape hNonlocal)
  · obtain ⟨φ⟩ := hModel
    have φ' : Hᶜ ≃g bilinearFormsGraph F m :=
      Eq.ndrec (motive := fun K => Hᶜ ≃g K)
        (complHostIso φ) (compl_compl (bilinearFormsGraph F m))
    have hLocalIso : localGraph H (e root) ≃g (nonlocalGraph Hᶜ (e root))ᶜ := by
      exact Eq.ndrec (motive := fun K : SimpleGraph W =>
        localGraph K (e root) ≃g (nonlocalGraph Hᶜ (e root))ᶜ)
        (localComplIso Hᶜ (e root)) (compl_compl H)
    have hNonlocalIso : nonlocalGraph H (e root) ≃g (localGraph Hᶜ (e root))ᶜ := by
      exact Eq.ndrec (motive := fun K : SimpleGraph W =>
        nonlocalGraph K (e root) ≃g (localGraph Hᶜ (e root))ᶜ)
        (nonlocalComplIso Hᶜ (e root)) (compl_compl H)
    let ψOne : nonlocalGraph H (e root) ≃g (bilinearFormsRankOneGraph F m)ᶜ :=
      hNonlocalIso.trans (complHostIso (bilinearLocalIso φ' (e root)))
    let ψTwo : localGraph H (e root) ≃g (bilinearFormsRankTwoGraph F m)ᶜ :=
      hLocalIso.trans (complHostIso (bilinearNonlocalIso φ' (e root)))
    have hExclude := not_cliqueUnionOrCover_of_fiveCycle
      ((SimpleGraph.Iso.toEmbedding ψTwo.symm).comp ((Embedding.complEquiv cycle).comp cycleFive_complEmbedding))
    rcases hEither with hLocal | hNonlocal
    · exact hExclude (hLocalShape hLocal)
    · have hOrder := Nat.card_congr ψOne.toEquiv
      have hEven := Nat.card_congr ψTwo.toEquiv
      obtain ⟨n, hn⟩ := hRankTwo
      have hNonlocalBound := cover_bound_of_large_induced_path_four
        (nonlocalGraph G root) (nonlocalGraph H (e root)) _
        (nonlocal_eppa G H e hEppa root) (nonlocalGraph_transitive H hRank (e root))
        ((SimpleGraph.Iso.toEmbedding ψOne.symm).comp ((Embedding.complEquiv path).comp pathFour_complEmbedding))
        (by omega) hGardiner (hNonlocalShape hNonlocal)
      exact hExclude (hLocalShape (by omega))

end EPPAIII.Primitive
