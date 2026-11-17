import EPPAIII.Primitive.UnitaryFourTwoModel
import EPPAIII.EPPA.Definitions
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Equiv.Fintype

/-! # Local obstructions in the order-45 unitary point graph -/

namespace EPPAIII.Primitive.UnitaryFourTwo

private def pointed (a : Fin n → Fin 12) : Fin (n+1) → Fin 45 :=
  Fin.cons root (localPoint ∘ a)

private def tripleCount (a : Fin 3 → Fin 45) : ℕ :=
  (Finset.univ.filter fun x => ∀ i, graph.Adj (a i) x).card

private def corner (a : Fin 4 → Fin 45) (x : Fin 45) : Prop :=
  x ≠ root ∧ (graph.Adj (a 0) x ∨ graph.Adj (a 1) x) ∧
    (graph.Adj (a 2) x ∨ graph.Adj (a 3) x)

private instance (a : Fin 4 → Fin 45) : DecidablePred (corner a) := by
  intro x
  unfold corner
  infer_instance

private def cornerEdgeCount (a : Fin 4 → Fin 45) : ℕ :=
  ((Finset.univ : Finset (Fin 45 × Fin 45)).filter fun (x,y) =>
    corner a x ∧ corner a y ∧ graph.Adj x y).card

private theorem card_filter_invariant {W : Type*} [Fintype W]
    (q : Equiv.Perm W) (P Q : W → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x ↔ Q (q x)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  classical
  have hMap : (Finset.univ.filter P).map q.toEmbedding = Finset.univ.filter Q := by
    ext y
    obtain ⟨x,rfl⟩ := q.surjective y
    simp [← h x]
  rw [← hMap, Finset.card_map]

private theorem tripleCount_invariant (q : Equiv.Perm (Fin 45))
    (hq : IsGraphAutomorphism graph q) (a b : Fin 3 → Fin 45)
    (h : ∀ i, q (a i) = b i) : tripleCount a = tripleCount b := by
  apply card_filter_invariant q
  intro x
  simpa only [← h] using (forall_congr' fun i => hq (a i) x)

private theorem cornerEdgeCount_invariant (q : Equiv.Perm (Fin 45))
    (hq : IsGraphAutomorphism graph q) (hRoot : q root = root) (a b : Fin 4 → Fin 45)
    (h : ∀ i, q (a i) = b i) : cornerEdgeCount a = cornerEdgeCount b := by
  have hCorner (x : Fin 45) : corner a x ↔ corner b (q x) := by
    have hNe : x ≠ root ↔ q x ≠ root := by
      simpa only [hRoot] using (q.injective.ne_iff.symm : x ≠ root ↔ q x ≠ q root)
    have hAdj (i : Fin 4) : graph.Adj (a i) x ↔ graph.Adj (b i) (q x) := by
      simpa only [h i] using hq (a i) x
    exact and_congr hNe (and_congr (or_congr (hAdj 0) (hAdj 1)) (or_congr (hAdj 2) (hAdj 3)))
  apply card_filter_invariant (q.prodCongr q)
  intro x
  exact and_congr (hCorner x.1) (and_congr (hCorner x.2) (hq _ _))

private def tupleMatched (a b : Fin n → Fin 45) : Prop :=
  Function.Injective a ∧ Function.Injective b ∧
    ∀ i j, graph.Adj (a i) (a j) ↔ graph.Adj (b i) (b j)

private instance (a b : Fin n → Fin 45) : Decidable (tupleMatched a b) := by
  unfold tupleMatched
  infer_instance

private abbrev LocalPair (n : ℕ) := (Fin n → Fin 12) × (Fin n → Fin 12)

-- These pairs cover the seven-element selections with three occupied cliques.
private def triplePairs : List (LocalPair 3) :=
  [(![1, 2, 3], ![0, 1, 2]),
   (![4, 6, 8], ![6, 7, 8]),
   (![5, 9, 10], ![9, 10, 11]),
   (![0, 4, 5], ![3, 4, 5]),
   (![1, 2, 9], ![2, 7, 9]),
   (![6, 8, 10], ![0, 8, 10]),
   (![1, 3, 11], ![1, 6, 11]),
   (![2, 4, 9], ![4, 8, 9]),
   (![2, 3, 7], ![2, 3, 10]),
   (![0, 7, 11], ![0, 4, 11]),
   (![1, 5, 6], ![1, 5, 9]),
   (![0, 7, 8], ![0, 5, 7]),
   (![4, 5, 6], ![2, 4, 6]),
   (![3, 8, 10], ![1, 3, 8]),
   (![7, 9, 11], ![3, 7, 11]),
   (![6, 10, 11], ![1, 6, 11]),
   (![5, 6, 7], ![5, 6, 10]),
   (![0, 1, 11], ![0, 1, 2]),
   (![3, 10, 11], ![2, 3, 10]),
   (![1, 8, 9], ![4, 8, 9]),
   (![2, 6, 7], ![2, 7, 9]),
   (![3, 4, 8], ![3, 4, 5]),
   (![0, 2, 10], ![0, 1, 2]),
   (![1, 3, 5], ![1, 5, 9]),
   (![0, 4, 8], ![0, 4, 11]),
   (![1, 3, 11], ![3, 7, 11]),
   (![0, 10, 11], ![9, 10, 11]),
   (![0, 1, 5], ![0, 5, 7]),
   (![3, 4, 8], ![4, 8, 9])]

-- These pairs cover the remaining seven-element selections.
private def disjointEdgePairs : List (LocalPair 4) :=
  [(![3, 9, 4, 10], ![0, 9, 4, 10]),
   (![2, 11, 6, 3], ![0, 6, 2, 11]),
   (![1, 7, 5, 8], ![1, 7, 5, 2]),
   (![1, 7, 6, 9], ![0, 9, 7, 1]),
   (![2, 8, 3, 9], ![3, 9, 8, 5]),
   (![1, 10, 6, 3], ![3, 6, 4, 10]),
   (![2, 5, 7, 10], ![2, 5, 4, 10]),
   (![1, 10, 8, 11], ![4, 10, 8, 11]),
   (![2, 5, 6, 9], ![0, 9, 5, 2]),
   (![3, 6, 5, 11], ![3, 6, 8, 11])]

private def TripleObstruction (p : LocalPair 3) : Prop :=
  tupleMatched (pointed p.1) (pointed p.2) ∧
    tripleCount (localPoint ∘ p.1) ≠ tripleCount (localPoint ∘ p.2)

private instance (p : LocalPair 3) : Decidable (TripleObstruction p) := by
  unfold TripleObstruction
  infer_instance

private def EdgeObstruction (p : LocalPair 4) : Prop :=
  tupleMatched (pointed p.1) (pointed p.2) ∧
    cornerEdgeCount (localPoint ∘ p.1) ≠ cornerEdgeCount (localPoint ∘ p.2)

private instance (p : LocalPair 4) : Decidable (EdgeObstruction p) := by
  unfold EdgeObstruction
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem triplePairs_certified :
    triplePairs.all (fun p => decide (TripleObstruction p)) = true := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem disjointEdgePairs_certified :
    disjointEdgePairs.all (fun p => decide (EdgeObstruction p)) = true := by
  decide

private def pairSupport (s : Finset (Fin 12)) (p : LocalPair n) : Prop :=
  ∀ i, p.1 i ∈ s ∧ p.2 i ∈ s

private instance (s : Finset (Fin 12)) (p : LocalPair n) : Decidable (pairSupport s p) := by
  unfold pairSupport
  infer_instance

private abbrev selections : Finset (Finset (Fin 12)) := Finset.univ.powersetCard 7

private def covered (s : Finset (Fin 12)) : Bool :=
  triplePairs.any (fun p => decide (pairSupport s p)) ||
    disjointEdgePairs.any (fun p => decide (pairSupport s p))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
private theorem certificate_coverage : ∀ s : selections, covered s.val = true := by
  decide

private theorem eppa_matched_tuples {V : Type*} [Finite V]
    (G : SimpleGraph V) (e : V ↪ Fin 45) (hEPPA : IsEPPAEmbedding G graph e)
    (a b : Fin n → Fin 45) (h : tupleMatched a b)
    (hA : ∀ i, a i ∈ Set.range e) (hB : ∀ i, b i ∈ Set.range e) :
    ∃ q : Equiv.Perm (Fin 45), IsGraphAutomorphism graph q ∧ ∀ i, q (a i) = b i := by
  classical
  let a' (i : Fin n) := (hA i).choose
  let b' (i : Fin n) := (hB i).choose
  have ha (i : Fin n) : e (a' i) = a i := (hA i).choose_spec
  have hb (i : Fin n) : e (b' i) = b i := (hB i).choose_spec
  have ha' : Function.Injective a' := fun i j hEq => h.1
    ((ha i).symm.trans ((congrArg e hEq).trans (ha j)))
  have hb' : Function.Injective b' := fun i j hEq => h.2.1
    ((hb i).symm.trans ((congrArg e hEq).trans (hb j)))
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair a' b' ha' hb'
  let D := Finset.univ.image a'
  have hPartial : IsPartialGraphAutomorphism G D p := by
    intro x y hx hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    rw [hp, hp, hEPPA.1, hEPPA.1, ha, ha, hb, hb]
    exact h.2.2 i j
  obtain ⟨q, hq, hExt⟩ := hEPPA.2 D p hPartial
  refine ⟨q,hq,fun i => ?_⟩
  rw [← ha, hExt (a' i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩), hp, hb]

private theorem pointed_in_selection {V : Type*} (e : V ↪ Fin 45)
    (hRoot : root ∈ Set.range e) (s : Finset (Fin 12))
    (hSelection : ∀ i ∈ s, localPoint i ∈ Set.range e) (a : Fin n → Fin 12)
    (hA : ∀ i, a i ∈ s) (i : Fin (n + 1)) : pointed a i ∈ Set.range e := by
  refine Fin.cases hRoot (fun j => ?_) i
  exact hSelection _ (hA j)

/-- Every seven selected local vertices preclude an EPPA embedding
when the root is the chosen coordinate point. -/
theorem local_order_le_six {V : Type*} [Finite V] (G : SimpleGraph V)
    (e : V ↪ Fin 45) (hEPPA : IsEPPAEmbedding G graph e)
    (v : V) (hRoot : e v = root) : Nat.card (G.neighborSet v) ≤ 6 := by
  classical
  let := Fintype.ofFinite (G.neighborSet v)
  by_contra! hLarge
  have hx (x : G.neighborSet v) : graph.Adj root (e x) :=
    hRoot ▸ (hEPPA.1 v x).mp x.property
  let loc (x : G.neighborSet v) : Fin 12 := ((localPoint_range _).mp (hx x)).choose
  have hLoc (x : G.neighborSet v) : localPoint (loc x) = e x :=
    ((localPoint_range _).mp (hx x)).choose_spec
  let f : G.neighborSet v ↪ Fin 12 :=
    ⟨loc, fun x y hEq => Subtype.ext (e.injective
      ((hLoc x).symm.trans ((congrArg localPoint hEq).trans (hLoc y))))⟩
  let S := Finset.univ.map f
  have hCard : 7 ≤ S.card := by
    rw [Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq hCard
  have hSel (i : Fin 12) (hi : i ∈ T) : localPoint i ∈ Set.range e := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp (hTS hi)
    exact ⟨x.val,(hLoc x).symm⟩
  have hr : root ∈ Set.range e := ⟨v,hRoot⟩
  have hCheck := certificate_coverage ⟨T, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _,hT⟩⟩
  change covered T = true at hCheck
  unfold covered at hCheck
  rcases Bool.or_eq_true_iff.mp hCheck with hTriple | hEdge
  · obtain ⟨p,hp,hSupport⟩ := List.any_eq_true.mp hTriple
    have hs : pairSupport T p := of_decide_eq_true hSupport
    have hGood : TripleObstruction p := of_decide_eq_true
      (List.all_eq_true.mp triplePairs_certified _ hp)
    obtain ⟨q,hq,hMap⟩ := eppa_matched_tuples G e hEPPA _ _ hGood.1
      (pointed_in_selection e hr T hSel _ (fun i => (hs i).1))
      (pointed_in_selection e hr T hSel _ (fun i => (hs i).2))
    exact hGood.2 (tripleCount_invariant q hq _ _ (fun i => hMap i.succ))
  · obtain ⟨p,hp,hSupport⟩ := List.any_eq_true.mp hEdge
    have hs : pairSupport T p := of_decide_eq_true hSupport
    have hGood : EdgeObstruction p := of_decide_eq_true
      (List.all_eq_true.mp disjointEdgePairs_certified _ hp)
    obtain ⟨q,hq,hMap⟩ := eppa_matched_tuples G e hEPPA _ _ hGood.1
      (pointed_in_selection e hr T hSel _ (fun i => (hs i).1))
      (pointed_in_selection e hr T hSel _ (fun i => (hs i).2))
    exact hGood.2 (cornerEdgeCount_invariant q hq (hMap 0) _ _ (fun i => hMap i.succ))

end EPPAIII.Primitive.UnitaryFourTwo
