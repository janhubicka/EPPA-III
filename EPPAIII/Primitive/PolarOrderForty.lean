import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.PolarRankTwoConstituent

/-! # Finite rooted action checks for the two polar graphs of order 40 -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- Each partial automorphism of a local selection must extend to a host
automorphism fixing the specified root. -/
def HasRootedLocalExtensions {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (root : W) : Prop :=
  ∀ (D : Finset V) (p : Equiv.Perm V), IsPartialGraphAutomorphism G D p →
    ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q root = root ∧
      ∀ x ∈ D, q (e x) = e (p x)

private theorem rooted_local_extensions_of_eppa {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hEPPA : IsEPPAEmbedding G H e) (r : V) :
    HasRootedLocalExtensions (localGraph G r) H
      ((Function.Embedding.subtype (· ∈ G.neighborSet r)).trans e) (e r) := by
  classical
  intro D p hPart
  let p' : Equiv.Perm V := Equiv.Perm.ofSubtype p
  let D' := insert r (D.image Subtype.val)
  have hFix : p' r = r := Equiv.Perm.ofSubtype_apply_of_not_mem p (G.loopless.irrefl r)
  have hOn (x : G.neighborSet r) : p' x = ↑(p x) :=
    Equiv.Perm.ofSubtype_apply_coe p x
  have hPart' : IsPartialGraphAutomorphism G D' p' := by
    intro x y hx hy
    rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [hFix]
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hy
      rw [hFix, hOn y]
      exact iff_of_true y.property (p y).property
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
      rw [hFix, hOn x]
      exact iff_of_true (G.adj_symm x.property) (G.adj_symm (p x).property)
    · obtain ⟨x, hxD, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y, hyD, rfl⟩ := Finset.mem_image.mp hy
      rw [hOn x, hOn y]
      exact hPart x y hxD hyD
  obtain ⟨q, hq, hExtend⟩ := hEPPA.2 D' p' hPart'
  refine ⟨q, hq, ?_, ?_⟩
  · simpa only [hFix] using hExtend r (Finset.mem_insert_self _ _)
  · intro x hx
    change q (e x) = e (p x)
    simpa only [hOn x] using
      hExtend x (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx))

/-- The finite check uses only the selected neighbourhood at each root.
The two coordinate models satisfy this predicate by exact enumeration of
the rooted actions and the compatible local masks. -/
def OrderFortyPolarLocalCheck {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ S : Set W, 20 ≤ Nat.card S →
    (∀ r : S, 6 ≤ Nat.card ((H.induce S).neighborSet r)) →
    ¬ (∀ r : S, HasRootedLocalExtensions (localGraph (H.induce S) r) H
      ((Function.Embedding.subtype (· ∈ (H.induce S).neighborSet r)).trans
        (Function.Embedding.subtype (· ∈ S))) r.val)

/-- For either symplectic rank-two order-40 model, the nonlocal model
test forces a local half-selection at every selected root. The finite
rooted check then excludes the actual embedding. -/
theorem polarSymplecticThree_not_eppa {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (hEPPA : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hSRG : H.IsSRGWith 40 12 2 4) (hCheck : OrderFortyPolarLocalCheck H)
    (hShapes : ∀ r : V,
      Nat.card {x : W // e r ≠ x ∧ ¬ H.Adj (e r) x} ≤
        2 * Nat.card {x : V // r ≠ x ∧ ¬ G.Adj r x} →
      let J := nonlocalGraph H (e r)
      (∃ s t, Nonempty (J ≃g cliqueUnion s t) ∨ Nonempty (J ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (J ≃g coverGraph s t X Y) ∨
        Nonempty (J ≃g (coverGraph s t X Y)ᶜ))) : False := by
  classical
  let := Fintype.ofFinite V
  have hOrder : Nat.card W = 40 := Nat.card_eq_fintype_card.trans hSRG.card
  have hMinimum (r : V) : 6 ≤ Nat.card (G.neighborSet r) := by
    by_contra! hSmall
    have hLocal : Nat.card (H.neighborSet (e r)) = 12 :=
      Nat.card_eq_fintype_card.trans ((H.card_neighborSet_eq_degree _).trans (hSRG.regular _))
    have hHostSplit := order_eq_one_add_subconstituent_orders H (e r)
    have hBaseSplit := order_eq_one_add_subconstituent_orders G r
    have hLarge : Nat.card {x : W // e r ≠ x ∧ ¬ H.Adj (e r) x} ≤
      2 * Nat.card {x : V // r ≠ x ∧ ¬ G.Adj r x} := by omega
    have hRange : RankTwoPolarRange 3 3 := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    obtain ⟨hC, hCC, hG, hCG⟩ :=
      polar_rankTwo_actual_second_constituent_excludes_forms H hRange hSRG (e r)
    rcases hShapes r hLarge with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
    · rcases h with ⟨f⟩ | ⟨f⟩
      · exact (hC s t).false (Classical.choice f)
      · exact (hCC s t).false (Classical.choice f)
    · rcases h with ⟨f⟩ | ⟨f⟩
      · exact (hG s t X Y).false (Classical.choice f)
      · exact (hCG s t X Y).false (Classical.choice f)
  let S := Set.range e
  let := Fintype.ofFinite S
  let φ : V ≃ S := Equiv.ofInjective e e.injective
  let ψ : G ≃g H.induce S := ⟨φ, fun {a b} => (hEPPA.1 a b).symm⟩
  have hSelected : 20 ≤ Nat.card S := by
    have hCard := Nat.card_congr φ
    omega
  have hRootedMinimum (r : S) : 6 ≤ Nat.card ((H.induce S).neighborSet r) :=
    (hMinimum (ψ.symm r)).trans_eq (Nat.card_congr (ψ.symm.mapNeighborSet r)).symm
  let eS : S ↪ W := Function.Embedding.subtype _
  have hMap : relabelEmbedding e φ.symm = eS := by
    ext x
    exact congrArg Subtype.val (φ.apply_symm_apply x)
  have hRangeEPPA : IsEPPAEmbedding (H.induce S) H eS := by
    rw [← hMap]
    exact eppa_relabel_base G H e hEPPA φ.symm (H.induce S)
      (fun _ _ => ψ.symm.map_adj_iff.symm)
  exact hCheck S hSelected hRootedMinimum
    (fun r => rooted_local_extensions_of_eppa (H.induce S) H eS hRangeEPPA r)

end EPPAIII.Primitive
