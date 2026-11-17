import EPPAIII.Primitive.Subconstituents

/-!
# Half-order inheritance and the subconstituent bound

These proofs count the actual selected sets in the two subconstituents and
also establish the assertions with the maximum EPPA base order.
-/

namespace EPPAIII.Primitive

variable {V W : Type*}

theorem order_eq_one_add_subconstituent_orders [Finite V]
    (H : SimpleGraph V) (root : V) :
    Nat.card V =
      1 + Nat.card (H.neighborSet root) + Nat.card {x : V // root ≠ x ∧ ¬ H.Adj root x} := by
  classical
  let N := H.neighborSet root
  let C := {x : (Nᶜ : Set V) | x.val = root}
  have hSplit := Nat.card_congr (Equiv.Set.sumCompl N)
  rw [Nat.card_sum] at hSplit
  have hSplit' := Nat.card_congr (Equiv.Set.sumCompl C)
  rw [Nat.card_sum] at hSplit'
  have hOne : Nat.card C = 1 := by
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨⟨root, H.loopless.irrefl root⟩, rfl⟩, ?_⟩
    intro x
    exact Subtype.ext (Subtype.ext x.property)
  let f : (Cᶜ : Set (Nᶜ : Set V)) ≃ {x : V // root ≠ x ∧ ¬ H.Adj root x} := {
    toFun x := ⟨x.val.val, Ne.symm x.property, x.val.property⟩
    invFun x := ⟨⟨x.val, x.property.2⟩, Ne.symm x.property.1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hC := Nat.card_congr f
  change Nat.card V = 1 + Nat.card N + _
  omega

private def hasEppaBaseOfOrder (H : SimpleGraph V) (n : Nat) : Prop :=
  ∃ S : Set V, Nat.card S = n ∧ IsEPPAEmbedding (H.induce S) H (Function.Embedding.subtype _)

/-- The maximal order of an induced subgraph for which H is an EPPA witness. -/
noncomputable def maxEppaOrder [Finite V] (H : SimpleGraph V) : Nat := by
  classical
  exact Nat.findGreatest (hasEppaBaseOfOrder H) (Nat.card V)

theorem maxEppaOrder_attained [Finite V] (H : SimpleGraph V) :
    ∃ S : Set V, Nat.card S = maxEppaOrder H ∧
      IsEPPAEmbedding (H.induce S) H (Function.Embedding.subtype _) := by
  classical
  change hasEppaBaseOfOrder H (maxEppaOrder H)
  unfold maxEppaOrder
  apply Nat.findGreatest_spec (m := 0) (Nat.zero_le _)
  refine ⟨∅, Nat.card_of_isEmpty, ?_⟩
  refine ⟨fun x _ => x.property.elim, fun _ _ _ => ⟨1, ?_, fun x _ => x.property.elim⟩⟩
  intro x y
  rfl

theorem order_le_maxEppaOrder [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) :
    Nat.card V ≤ maxEppaOrder H := by
  classical
  unfold maxEppaOrder
  apply Nat.le_findGreatest (Nat.card_le_card_of_injective e e.injective)
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite (Set.range e)
  let f := Equiv.ofInjective e e.injective
  have hMap (x : Set.range e) : e (f.symm x) = x := congrArg Subtype.val (f.apply_symm_apply x)
  have hEPPA := eppa_relabel_base G H e heppa f.symm (H.induce (Set.range e)) (by
    intro x y
    change H.Adj (↑x) (↑y) ↔ G.Adj (f.symm x) (f.symm y)
    rw [heppa.1 (f.symm x) (f.symm y), hMap, hMap])
  have heq : relabelEmbedding e f.symm = Function.Embedding.subtype _ := by
    ext x
    exact hMap x
  exact ⟨Set.range e, (Nat.card_congr f).symm, heq ▸ hEPPA⟩

/-- Move the image of the selected graph by a host automorphism. -/
private theorem eppa_comp_host_auto
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    IsEPPAEmbedding G H (e.trans q.toEmbedding) := by
  constructor
  · intro x y
    exact (heppa.1 x y).trans (hq (e x) (e y))
  · intro D p hp
    obtain ⟨r, hr, hExt⟩ := heppa.2 D p hp
    refine ⟨(q.symm.trans r).trans q, ?_, ?_⟩
    · intro x y
      change H.Adj x y ↔ H.Adj (q (r (q.symm x))) (q (r (q.symm y)))
      simpa using ((hq (q.symm x) (q.symm y)).symm.trans
        ((hr (q.symm x) (q.symm y)).trans (hq (r (q.symm x)) (r (q.symm y)))))
    · intro x hx
      change q (r (q.symm (q (e x)))) = q (e (p x))
      rw [q.symm_apply_apply, hExt x hx]

/-- The first assertion of Proposition local. -/
theorem maxEppaOrder_le_subconstituents [Finite W] (H : SimpleGraph W) (root : W)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y) :
    maxEppaOrder H ≤
      1 + maxEppaOrder (localGraph H root) + maxEppaOrder (nonlocalGraph H root) := by
  obtain ⟨S, hOrder, hEppa⟩ := maxEppaOrder_attained H
  by_cases hEmpty : IsEmpty S
  · letI := hEmpty
    rw [← hOrder, Nat.card_of_isEmpty]
    omega
  obtain ⟨x⟩ := not_isEmpty_iff.mp hEmpty
  obtain ⟨q, hq, hqRoot⟩ := hTrans x root
  let e := (Function.Embedding.subtype (· ∈ S)).trans q.toEmbedding
  have hEppa' : IsEPPAEmbedding (H.induce S) H e :=
    eppa_comp_host_auto (H.induce S) H _ hEppa q hq
  have hRoot : e x = root := hqRoot
  have hLocal := order_le_maxEppaOrder _ _ _ (local_eppa _ _ e hEppa' x)
  have hNonlocal := order_le_maxEppaOrder _ _ _ (nonlocal_eppa _ _ e hEppa' x)
  rw [hRoot] at hLocal hNonlocal
  change Nat.card {y : S // x ≠ y ∧ ¬ (H.induce S).Adj x y} ≤
    maxEppaOrder (nonlocalGraph H root) at hNonlocal
  have hSplit := order_eq_one_add_subconstituent_orders (H.induce S) x
  omega

private theorem not_both_subconstituents_odd [Finite W] (H : SimpleGraph W) (root : W)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y) :
    ¬ (Nat.card (H.neighborSet root) % 2 = 1 ∧
      Nat.card {x : W // root ≠ x ∧ ¬ H.Adj root x} % 2 = 1) := by
  classical
  letI := Fintype.ofFinite W
  rintro ⟨hLocal, hNonlocal⟩
  have hSplit := order_eq_one_add_subconstituent_orders H root
  have hOdd (x : W) : Odd (H.degree x) := by
    obtain ⟨q, hq, hqRoot⟩ := hTrans root x
    let g : H ≃g H := ⟨q, fun {a b} => (hq a b).symm⟩
    have hDegree := g.degree_eq root
    change H.degree (q root) = H.degree root at hDegree
    rw [hqRoot] at hDegree
    rw [hDegree, ← H.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    refine ⟨Nat.card (H.neighborSet root) / 2, ?_⟩
    omega
  have hShake := H.even_card_odd_degree_vertices
  have hEven : Even (Fintype.card W) := by
    simpa [hOdd] using hShake
  rw [← Nat.card_eq_fintype_card] at hEven
  obtain ⟨a, ha⟩ := hEven
  omega

/-- The half-order assertion for the actual selected copy at every selected root. -/
theorem selected_subconstituent_at_least_half [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (root : V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (hHalf : Nat.card W ≤ 2 * Nat.card V) :
    Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) ∨
      Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} := by
  have hW := order_eq_one_add_subconstituent_orders H (e root)
  have hV := order_eq_one_add_subconstituent_orders G root
  have hParity := not_both_subconstituents_odd H (e root) hTrans
  omega

/-- The second assertion of Proposition local, via the actual selected copy. -/
theorem subconstituent_has_half_order_eppa [Finite W] (H : SimpleGraph W) (root : W)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (hHalf : Nat.card W ≤ 2 * maxEppaOrder H) :
    Nat.card (H.neighborSet root) ≤ 2 * maxEppaOrder (localGraph H root) ∨
      Nat.card {x : W // root ≠ x ∧ ¬ H.Adj root x} ≤ 2 * maxEppaOrder (nonlocalGraph H root) := by
  have h := maxEppaOrder_le_subconstituents H root hTrans
  have hSplit := order_eq_one_add_subconstituent_orders H root
  have hParity := not_both_subconstituents_odd H root hTrans
  omega

/-- The corrected even-even alternative, before the rank-three reduction
identifies any strict-majority subconstituent. -/
theorem even_subconstituent_orders_strict_or_equal [Finite W] (H : SimpleGraph W) (root : W)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (hHalf : Nat.card W ≤ 2 * maxEppaOrder H)
    (hEvenL : Even (Nat.card (H.neighborSet root)))
    (hEvenN : Even (Nat.card {x : W // root ≠ x ∧ ¬ H.Adj root x})) :
    Nat.card (H.neighborSet root) < 2 * maxEppaOrder (localGraph H root) ∨
      Nat.card {x : W // root ≠ x ∧ ¬ H.Adj root x} < 2 * maxEppaOrder (nonlocalGraph H root) ∨
      (2 * maxEppaOrder (localGraph H root) = Nat.card (H.neighborSet root) ∧
        2 * maxEppaOrder (nonlocalGraph H root) =
          Nat.card {x : W // root ≠ x ∧ ¬ H.Adj root x}) := by
  have h := maxEppaOrder_le_subconstituents H root hTrans
  have hSplit := order_eq_one_add_subconstituent_orders H root
  obtain ⟨a, ha⟩ := hEvenL
  obtain ⟨b, hb⟩ := hEvenN
  omega

end EPPAIII.Primitive
