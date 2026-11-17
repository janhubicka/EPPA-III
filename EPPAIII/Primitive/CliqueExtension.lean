import EPPAIII.Primitive.NeighbourhoodBound
import EPPAIII.Primitive.LocalReduction
import EPPAIII.CliqueCovers.TwinQuotientAction

/-!
# EPPA for a clique extension and its projection

The fibres are the equal closed neighbourhood classes when the underlying
graph has no pair of distinct vertices with the same closed neighbourhood.
This is weaker than forbidding both adjacent and nonadjacent twins.
-/

namespace EPPAIII.Primitive

open EPPAIII.CliqueCovers

variable {I V : Type*}

/-- Replace each vertex of the original graph by a clique indexed by I. -/
def cliqueExtension (I : Type*) (H : SimpleGraph V) : SimpleGraph (I × V) where
  Adj x y := H.Adj x.2 y.2 ∨ (x.2 = y.2 ∧ x.1 ≠ y.1)
  symm := by
    constructor
    intro x y h
    exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr ⟨h.1.symm, h.2.symm⟩)
  loopless := by
    constructor
    intro x h
    exact h.elim (H.loopless.irrefl x.2) (fun h => h.2 rfl)

/-- A clique extension over nonempty fibres preserves connectedness. -/
theorem cliqueExtension_connected [Nonempty I] {H : SimpleGraph V}
    (hConnected : H.Connected) : (cliqueExtension I H).Connected := by
  have := hConnected.nonempty
  refine ⟨?_⟩
  intro x y
  let layer : H →g cliqueExtension I H :=
    ⟨fun v => (x.1, v), fun h => Or.inl h⟩
  have hWalk := (hConnected x.2 y.2).map layer
  have hEnd : (cliqueExtension I H).Reachable (x.1, y.2) y := by
    by_cases h : x.1 = y.1
    · rw [show (x.1, y.2) = y from Prod.ext h rfl]
    · exact (show (cliqueExtension I H).Adj (x.1, y.2) y from Or.inr ⟨rfl, h⟩).reachable
  exact hWalk.trans hEnd

private theorem cliqueExtension_closedNeighbourhood_iff (H : SimpleGraph V) (x y : I × V) :
    y ∈ closedNeighbourhood (cliqueExtension I H) x ↔
      y.2 ∈ closedNeighbourhood H x.2 := by
  classical
  change (y = x ∨ H.Adj x.2 y.2 ∨ (x.2 = y.2 ∧ x.1 ≠ y.1)) ↔
      (y.2 = x.2 ∨ H.Adj x.2 y.2)
  constructor
  · rintro (rfl | h | ⟨h, _⟩)
    · exact Or.inl rfl
    · exact Or.inr h
    · exact Or.inl h.symm
  · rintro (h | h)
    · by_cases hFirst : x.1 = y.1
      · exact Or.inl (Prod.ext hFirst.symm h)
      · exact Or.inr (Or.inr ⟨h.symm, hFirst⟩)
    · exact Or.inr (Or.inl h)

/-- The fibres of a clique extension are intrinsically definable when the
underlying graph has no pair of distinct adjacent twins. -/
theorem cliqueExtension_fibres (H : SimpleGraph V)
    (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (x y : I × V) :
    SameClosedNeighbourhood (cliqueExtension I H) x y ↔ x.2 = y.2 := by
  constructor
  · intro h
    apply hTwins
    unfold SameClosedNeighbourhood at h ⊢
    ext z
    rw [← cliqueExtension_closedNeighbourhood_iff H x (x.1, z),
      ← cliqueExtension_closedNeighbourhood_iff H y (x.1, z), h]
  · intro h
    unfold SameClosedNeighbourhood
    ext z
    rw [cliqueExtension_closedNeighbourhood_iff, cliqueExtension_closedNeighbourhood_iff, h]

private theorem cliqueExtension_auto_fibres (H : SimpleGraph V)
    (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (q : Equiv.Perm (I × V)) (hq : IsGraphAutomorphism (cliqueExtension I H) q)
    (x y : I × V) :
    (q x).2 = (q y).2 ↔ x.2 = y.2 :=
  (cliqueExtension_fibres H hTwins (q x) (q y)).symm.trans
    ((sameClosedNeighbourhood_aut_iff _ q hq x y).trans
      (cliqueExtension_fibres H hTwins x y))

/-- A clique extension automorphism induces an automorphism on the quotient. -/
private theorem cliqueExtension_auto_descends (H : SimpleGraph V)
    (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (i : I) (q : Equiv.Perm (I × V)) (hq : IsGraphAutomorphism (cliqueExtension I H) q) :
    ∃ p : Equiv.Perm V, IsGraphAutomorphism H p ∧ ∀ x, (q x).2 = p x.2 := by
  let p : Equiv.Perm V := {
    toFun x := (q (i, x)).2
    invFun x := (q.symm (i, x)).2
    left_inv x := by
      change (q.symm (i, (q (i, x)).2)).2 = x
      have hf := cliqueExtension_auto_fibres H hTwins q.symm
        (graphAutomorphism_symm _ q hq) (i, (q (i, x)).2) (q (i, x))
      simpa using hf.mpr rfl
    right_inv x := by
      change (q (i, (q.symm (i, x)).2)).2 = x
      have hf := cliqueExtension_auto_fibres H hTwins q hq
        (i, (q.symm (i, x)).2) (q.symm (i, x))
      simpa using hf.mpr rfl }
  have hProj (x : I × V) : (q x).2 = p x.2 :=
    (cliqueExtension_auto_fibres H hTwins q hq x (i, x.2)).mpr rfl
  refine ⟨p, ?_, hProj⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  have hImage : (q (i, x)).2 ≠ (q (i, y)).2 := p.injective.ne hxy
  simpa [cliqueExtension, hxy, hImage, p] using hq (i, x) (i, y)

/-- Project an induced subgraph of a clique extension to the original graph. -/
def cliqueExtensionProjection (S : Set (I × V)) : Set V :=
  Prod.snd '' S

/-- The projection of any selected EPPA base is an EPPA base in the
underlying graph. For a partial automorphism on the projection, choose
one selected representative per fibre. -/
theorem cliqueExtension_projection_eppa [Nonempty I]
    (H : SimpleGraph V) (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (S : Set (I × V))
    (heppa : IsEPPAEmbedding ((cliqueExtension I H).induce S) (cliqueExtension I H)
      (Function.Embedding.subtype (· ∈ S))) :
    IsEPPAEmbedding (H.induce (cliqueExtensionProjection S)) H
      (Function.Embedding.subtype (· ∈ cliqueExtensionProjection S)) := by
  classical
  let P := cliqueExtensionProjection S
  have hExists (x : P) : ∃ s : S, s.val.2 = x.val := by
    obtain ⟨s, hs, hp⟩ := x.property
    exact ⟨⟨s, hs⟩, hp⟩
  let chooseRep (x : P) : S := Classical.choose (hExists x)
  have hRep (x : P) : (chooseRep x).val.2 = x.val := Classical.choose_spec (hExists x)
  have hInj : Function.Injective chooseRep := by
    intro x y h
    apply Subtype.ext
    exact ((hRep x).symm.trans (congrArg (fun v : S => v.val.2) h)).trans (hRep y)
  let r := Equiv.ofInjective chooseRep hInj
  have hAdj (x y : P) : (H.induce P).Adj x y ↔
      ((cliqueExtension I H).induce S).Adj (chooseRep x) (chooseRep y) := by
    by_cases hxy : x = y
    · subst y
      simp
    have hDistinct : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    change H.Adj x.val y.val ↔
      H.Adj (chooseRep x).val.2 (chooseRep y).val.2 ∨
        ((chooseRep x).val.2 = (chooseRep y).val.2 ∧
          (chooseRep x).val.1 ≠ (chooseRep y).val.1)
    rw [hRep x, hRep y]
    simp [hDistinct]
  refine ⟨fun _ _ => Iff.rfl, ?_⟩
  intro D p hp
  let p' : Equiv.Perm S := Equiv.Perm.ofSubtype ((r.symm.trans p).trans r)
  let D' := D.image chooseRep
  have hAction (x : P) : p' (chooseRep x) = chooseRep (p x) := by
    change (Equiv.Perm.ofSubtype ((r.symm.trans p).trans r)) (r x).val = chooseRep (p x)
    rw [Equiv.Perm.ofSubtype_apply_coe]
    change (r (p (r.symm (r x)))).val = _
    rw [r.symm_apply_apply]
    rfl
  have hPartial : IsPartialGraphAutomorphism ((cliqueExtension I H).induce S) D' p' := by
    intro x y hx hy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    rw [hAction a, hAction b]
    exact (hAdj a b).symm.trans ((hp a b ha hb).trans (hAdj (p a) (p b)))
  obtain ⟨q, hq, hExt⟩ := heppa.2 D' p' hPartial
  obtain ⟨q', hq', hProj⟩ := cliqueExtension_auto_descends H hTwins
    (Classical.choice ‹Nonempty I›) q hq
  refine ⟨q', hq', ?_⟩
  intro x hx
  have hxD : chooseRep x ∈ D' := Finset.mem_image_of_mem _ hx
  have hqMap : q (chooseRep x).val = (chooseRep (p x)).val := by
    have h := hExt (chooseRep x) hxD
    change q (chooseRep x).val = (p' (chooseRep x)).val at h
    rw [hAction] at h
    exact h
  calc
    q' x.val = q' (chooseRep x).val.2 := congrArg q' (hRep x).symm
    _ = (q (chooseRep x).val).2 := (hProj (chooseRep x).val).symm
    _ = (chooseRep (p x)).val.2 := congrArg Prod.snd hqMap
    _ = (p x).val := hRep (p x)

/-- The projection cardinality bounds the number of selected points after
multiplication by the size of a fibre. -/
theorem cliqueExtension_maxEppaOrder_le [Finite I] [Finite V] [Nonempty I]
    (H : SimpleGraph V) (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y) :
    maxEppaOrder (cliqueExtension I H) ≤ Nat.card I * maxEppaOrder H := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained (cliqueExtension I H)
  let lift (x : S) : I × cliqueExtensionProjection S :=
    (x.val.1, ⟨x.val.2, ⟨x.val, x.property, rfl⟩⟩)
  have hInj : Function.Injective lift := by
    intro x y eq
    exact Subtype.ext (Prod.ext (congrArg (fun a : I × cliqueExtensionProjection S => a.1) eq)
      (congrArg (fun a : I × cliqueExtensionProjection S => a.2.val) eq))
  have hSize := Nat.card_le_card_of_injective lift hInj
  rw [Nat.card_prod, hCard] at hSize
  exact hSize.trans (Nat.mul_le_mul_left _ (order_le_maxEppaOrder _ _ _
    (cliqueExtension_projection_eppa H hTwins S heppa)))

private theorem cliqueExtension_same_fibre_of_selected_adjacency
    (H : SimpleGraph V) (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (S : Set (I × V))
    (heppa : IsEPPAEmbedding ((cliqueExtension I H).induce S) (cliqueExtension I H)
      (Function.Embedding.subtype (· ∈ S))) (a a' b : S)
    (haa' : a ≠ a') (hSame : a'.val.2 = a.val.2)
    (hAdj : ((cliqueExtension I H).induce S).Adj a b) :
    b.val.2 = a.val.2 := by
  classical
  let G := (cliqueExtension I H).induce S
  have ha'b : G.Adj a' a := by
    refine Or.inr ⟨hSame, ?_⟩
    intro h
    exact haa' (Subtype.ext (Prod.ext h.symm hSame.symm))
  obtain ⟨q, hq, hMap, hFix⟩ :=
    eppa_same_profile_extension G _ _ heppa {a} a' b
      (by simpa using haa'.symm)
      (by simpa using (G.ne_of_adj hAdj).symm) (by
        intro u hu
        obtain rfl := Finset.mem_singleton.mp hu
        exact iff_of_true ha'b hAdj.symm)
  have hFibre := (cliqueExtension_auto_fibres H hTwins q hq a'.val a.val).mpr hSame
  change q a'.val = b.val at hMap
  have hFixA : q a.val = a.val := hFix a (Finset.mem_singleton_self _)
  simpa [hMap, hFixA] using hFibre

/-- In a connected selected EPPA base with a repeated fibre, every
vertex belongs to that fibre. With no repetition the projection is an
induced embedding of the entire selected graph. -/
theorem cliqueExtension_selected_order_le_of_connected [Finite I] [Finite V] [Nonempty I]
    (H : SimpleGraph V) (hTwins : ∀ x y, SameClosedNeighbourhood H x y → x = y)
    (S : Set (I × V))
    (heppa : IsEPPAEmbedding ((cliqueExtension I H).induce S) (cliqueExtension I H)
      (Function.Embedding.subtype (· ∈ S)))
    (hConnected : ((cliqueExtension I H).induce S).Connected) :
    Nat.card S ≤ max (Nat.card I) (maxEppaOrder H) := by
  classical
  by_cases hInj : Function.Injective (fun a : S => a.val.2)
  · let proj (a : S) : cliqueExtensionProjection S :=
      ⟨a.val.2, ⟨a.val, a.property, rfl⟩⟩
    have hCard := Nat.card_le_card_of_injective proj (fun _ _ h =>
      hInj (congrArg Subtype.val h))
    exact hCard.trans ((order_le_maxEppaOrder _ _ _
      (cliqueExtension_projection_eppa H hTwins S heppa)).trans (le_max_right _ _))
  · unfold Function.Injective at hInj
    push Not at hInj
    obtain ⟨x, y, hSame, hDistinct⟩ := hInj
    let G := (cliqueExtension I H).induce S
    have hPreserve (a b : S) (ha : a.val.2 = x.val.2) (hEdge : G.Adj a b) :
        b.val.2 = x.val.2 := by
      by_cases hA : a = x
      · subst a
        exact cliqueExtension_same_fibre_of_selected_adjacency H hTwins S heppa
          x y b hDistinct hSame.symm hEdge
      · exact (cliqueExtension_same_fibre_of_selected_adjacency H hTwins S heppa
          a x b hA ha.symm hEdge).trans ha
    have hWalk {a b : S} (p : G.Walk a b) :
        a.val.2 = x.val.2 → b.val.2 = x.val.2 := by
      induction p with
      | nil => exact id
      | cons h _ ih => exact fun ha => ih (hPreserve _ _ ha h)
    have hAll (a : S) : a.val.2 = x.val.2 := by
      obtain ⟨p⟩ := hConnected.preconnected x a
      exact hWalk p rfl
    have hInjective : Function.Injective (fun a : S => a.val.1) := by
      intro a b hEq
      exact Subtype.ext (Prod.ext hEq ((hAll a).trans (hAll b).symm))
    exact (Nat.card_le_card_of_injective _ hInjective).trans (le_max_left _ _)

end EPPAIII.Primitive
