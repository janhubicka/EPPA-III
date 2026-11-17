import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Logic.Equiv.Option
import Mathlib.Data.Fintype.Pi

/-! # Recognition of the degree-ten Schläfli complement -/

namespace EPPAIII.Primitive

open SimpleGraph

private theorem unique_common {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 27 10 1 5) {x y a b : V}
    (hxy : H.Adj x y) (hxa : H.Adj x a) (hya : H.Adj y a)
    (hxb : H.Adj x b) (hyb : H.Adj y b) : a = b := by
  have hSub : Subsingleton (H.commonNeighbors x y) :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [h.of_adj _ _ hxy])
  exact congrArg Subtype.val (hSub.elim ⟨a, hxa, hya⟩ ⟨b, hxb, hyb⟩)

private noncomputable def third {V : Type*} [Fintype V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (h : H.IsSRGWith 27 10 1 5) {x y : V} (hxy : H.Adj x y) :
    H.commonNeighbors x y :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [h.of_adj _ _ hxy]; decide))

section Pairing

variable {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
  (h : H.IsSRGWith 27 10 1 5) {r : V}

private noncomputable def mate (x : H.neighborSet r) : H.neighborSet r :=
  ⟨(third H h x.property).val, (third H h x.property).property.1⟩

private theorem mate_adj (x : H.neighborSet r) : H.Adj x.val (mate H h x).val :=
  (third H h x.property).property.2

private theorem mate_involutive : Function.Involutive (mate (r := r) H h) := by
  intro x
  apply Subtype.ext
  exact unique_common H h (mate H h x).property (mate H h (mate H h x)).property
    (mate_adj H h (mate H h x)) x.property (mate_adj H h x).symm

private theorem local_adj_iff_mate (x y : H.neighborSet r) :
    H.Adj x.val y.val ↔ y = mate H h x := by
  constructor
  · intro hxy
    apply Subtype.ext
    exact unique_common H h x.property y.property hxy (mate H h x).property (mate_adj H h x)
  · intro hy
    rw [hy]
    exact mate_adj H h x

private theorem no_both_endpoints (z : Hᶜ.neighborSet r) (x : H.neighborSet r)
    (hxa : H.Adj z.val x.val) (hxb : H.Adj z.val (mate H h x).val) : False :=
  z.property.1 (unique_common H h (mate_adj H h x) x.property.symm
    (mate H h x).property.symm hxa.symm hxb.symm)

private noncomputable def endpoint (z : Hᶜ.neighborSet r) :
    H.commonNeighbors r z.val × Bool → H.neighborSet r := fun (v, b) =>
  let p : H.neighborSet r := ⟨v.val, v.property.1⟩
  if b then mate H h p else p

private theorem endpoint_bijective (z : Hᶜ.neighborSet r) :
    Function.Bijective (endpoint H h z) := by
  classical
  have hInj : Function.Injective (endpoint H h z) := by
    rintro ⟨a, ba⟩ ⟨b, bb⟩ hab
    cases ba <;> cases bb
    · simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at hab
      exact Prod.ext (Subtype.ext (congrArg (fun w : H.neighborSet r => w.val) hab)) rfl
    · simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at hab
      have he : H.Adj z.val (mate H h ⟨b.val, b.property.1⟩).val := by
        rw [← hab]
        exact a.property.2
      exact (no_both_endpoints H h z ⟨b.val, b.property.1⟩ b.property.2 he).elim
    · simp only [endpoint, Bool.false_eq_true, ↓reduceIte] at hab
      have he : H.Adj z.val (mate H h ⟨a.val, a.property.1⟩).val := by
        rw [hab]
        exact b.property.2
      exact (no_both_endpoints H h z ⟨a.val, a.property.1⟩ a.property.2 he).elim
    · simp only [endpoint, ↓reduceIte] at hab
      have he := (mate_involutive H h).injective hab
      exact Prod.ext (Subtype.ext (congrArg (fun w : H.neighborSet r => w.val) he)) rfl
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hInj, by rw [Fintype.card_prod, h.of_not_adj z.property.1 z.property.2,
        Fintype.card_bool, H.card_neighborSet_eq_degree, h.regular]⟩

private theorem choose_per_pair (z : Hᶜ.neighborSet r) (x : H.neighborSet r) :
    H.Adj z.val x.val ∨ H.Adj z.val (mate H h x).val := by
  obtain ⟨⟨v, b⟩, hb⟩ := (endpoint_bijective H h z).surjective x
  cases b
  · left
    change (⟨v.val, v.property.1⟩ : H.neighborSet r) = x at hb
    rw [← hb]
    exact v.property.2
  · right
    change mate H h ⟨v.val, v.property.1⟩ = x at hb
    rw [← hb, mate_involutive H h]
    exact v.property.2

private noncomputable def endpointIndex (z : Hᶜ.neighborSet r) :
    H.commonNeighbors r z.val ≃ Fin 5 := Fintype.equivFinOfCardEq
  (h.of_not_adj z.property.1 z.property.2)

private noncomputable def localChart (z : Hᶜ.neighborSet r) :
    Fin 5 × Bool ≃ H.neighborSet r :=
  (Equiv.prodCongr (endpointIndex H h z).symm (Equiv.refl Bool)).trans
    (Equiv.ofBijective (endpoint H h z) (endpoint_bijective H h z))

private theorem localChart_mate (z : Hᶜ.neighborSet r) (i : Fin 5) (b : Bool) :
    mate H h (localChart H h z (i, b)) = localChart H h z (i, !b) := by
  cases b
  · rfl
  · exact mate_involutive H h _

private theorem localChart_adj (z : Hᶜ.neighborSet r) (i j : Fin 5) (a b : Bool) :
    H.Adj (localChart H h z (i, a)).val (localChart H h z (j, b)).val ↔
      (j, b) = (i, !a) := by
  rw [local_adj_iff_mate H h, localChart_mate H h]
  exact (localChart H h z).injective.eq_iff

private theorem localChart_base_adj (z : Hᶜ.neighborSet r) (i : Fin 5) :
    H.Adj z.val (localChart H h z (i, false)).val :=
  ((endpointIndex H h z).symm i).property.2

private noncomputable def remoteCode (z u : Hᶜ.neighborSet r) (i : Fin 5) : Bool :=
  decide (H.Adj u.val (localChart H h z (i, true)).val)

private theorem remoteCode_adj (z u : Hᶜ.neighborSet r) (i : Fin 5) (b : Bool) :
    H.Adj u.val (localChart H h z (i, b)).val ↔ remoteCode H h z u i = b := by
  cases b
  · have hEither := choose_per_pair H h u (localChart H h z (i, false))
    have hNotBoth := no_both_endpoints H h u (localChart H h z (i, false))
    rw [localChart_mate H h] at hEither hNotBoth
    change H.Adj u.val (localChart H h z (i, false)).val ∨
      H.Adj u.val (localChart H h z (i, true)).val at hEither
    change H.Adj u.val (localChart H h z (i, false)).val →
      H.Adj u.val (localChart H h z (i, true)).val → False at hNotBoth
    simp only [remoteCode, decide_eq_false_iff_not]
    exact ⟨hNotBoth, fun h => hEither.resolve_right h⟩
  · simp [remoteCode]

private theorem remoteCode_zero (z : Hᶜ.neighborSet r) :
    remoteCode H h z z = fun _ => false := by
  funext i
  exact (remoteCode_adj H h z z i false).mp (localChart_base_adj H h z i)

private abbrev Bits := Fin 5 → Bool

private def flipExcept (i : Fin 5) (b : Bits) : Bits :=
  fun j => if j = i then b j else !b j

private theorem eq_flipExcept_of_agreement {a b : Bits} {i : Fin 5}
    (h : ∀ j, a j = b j ↔ j = i) : b = flipExcept i a := by
  funext j
  by_cases hj : j = i
  · simpa [flipExcept, hj] using ((h j).mpr hj).symm
  · have hb (x y : Bool) : x ≠ y → y = !x := by cases x <;> cases y <;> simp
    simpa [flipExcept, hj] using hb (a j) (b j) (fun he => hj ((h j).mp he))

private theorem remote_adj_unique_agreement (z u v : Hᶜ.neighborSet r)
    (huv : H.Adj u.val v.val) : ∃ i, ∀ j,
    remoteCode H h z u j = remoteCode H h z v j ↔ j = i := by
  classical
  let w := third H h huv
  have hAgreed (i : Fin 5) (he : remoteCode H h z u i = remoteCode H h z v i) :
      w.val = (localChart H h z (i, remoteCode H h z u i)).val := by
    exact unique_common H h huv w.property.1 w.property.2
      ((remoteCode_adj H h z u i _).mpr rfl) ((remoteCode_adj H h z v i _).mpr he.symm)
  have hSome : ∃ i, remoteCode H h z u i = remoteCode H h z v i := by
    by_contra! hNone
    have hNoLocal : ¬ H.Adj r w.val := by
      intro hrw
      obtain ⟨⟨i, b⟩, hi⟩ := (localChart H h z).surjective ⟨w.val, hrw⟩
      have hi' := congrArg (fun a : H.neighborSet r => a.val) hi
      apply hNone i
      exact ((remoteCode_adj H h z u i b).mp (hi'.symm ▸ w.property.1)).trans
        ((remoteCode_adj H h z v i b).mp (hi'.symm ▸ w.property.2)).symm
    have hrw : r ≠ w.val := by
      intro hrw
      exact u.property.2 (Eq.mp (congrArg (fun x : V => H.Adj x u.val) hrw.symm)
        w.property.1.symm)
    let ww : Hᶜ.neighborSet r := ⟨w.val, hrw, hNoLocal⟩
    let i : Fin 5 := 0
    let b := remoteCode H h z ww i
    let a := localChart H h z (i, b)
    have hwa : H.Adj w.val a.val := (remoteCode_adj H h z ww i b).mpr rfl
    have huorv : remoteCode H h z u i = b ∨ remoteCode H h z v i = b := by
      have hBool (a b c : Bool) : a ≠ b → a = c ∨ b = c := by
        cases a <;> cases b <;> cases c <;> simp
      exact hBool _ _ _ (hNone i)
    rcases huorv with hu | hv
    · have hua : H.Adj u.val a.val := (remoteCode_adj H h z u i b).mpr hu
      apply v.property.2
      rw [← unique_common H h w.property.1.symm hwa hua w.property.2.symm huv]
      exact a.property
    · have hva : H.Adj v.val a.val := (remoteCode_adj H h z v i b).mpr hv
      apply u.property.2
      rw [← unique_common H h w.property.2.symm hwa hva w.property.1.symm huv.symm]
      exact a.property
  obtain ⟨i, hi⟩ := hSome
  refine ⟨i, fun j => ⟨?_, ?_⟩⟩
  · intro hj
    have hp : localChart H h z (j, remoteCode H h z u j) =
        localChart H h z (i, remoteCode H h z u i) :=
      Subtype.ext ((hAgreed j hj).symm.trans (hAgreed i hi))
    exact congrArg Prod.fst ((localChart H h z).injective hp)
  · rintro rfl
    exact hi

private theorem remote_flip_neighbor (z u : Hᶜ.neighborSet r) (i : Fin 5) :
    ∃ v : Hᶜ.neighborSet r, H.Adj u.val v.val ∧
      remoteCode H h z v = flipExcept i (remoteCode H h z u) := by
  let b := remoteCode H h z u i
  let a := localChart H h z (i, b)
  have hua : H.Adj u.val a.val := (remoteCode_adj H h z u i b).mpr rfl
  let w := third H h hua
  have hrw : r ≠ w.val := by
    intro he
    exact u.property.2 (Eq.mp (congrArg (fun x : V => H.Adj x u.val) he.symm)
      w.property.1.symm)
  have hNoLocal : ¬ H.Adj r w.val := by
    intro hrw'
    have hw : (⟨w.val, hrw'⟩ : H.neighborSet r) = mate H h a :=
      (local_adj_iff_mate H h a ⟨w.val, hrw'⟩).mp w.property.2
    apply no_both_endpoints H h u a hua
    rw [← congrArg (fun y : H.neighborSet r => y.val) hw]
    exact w.property.1
  let v : Hᶜ.neighborSet r := ⟨w.val, hrw, hNoLocal⟩
  have hv : remoteCode H h z v i = b := (remoteCode_adj H h z v i b).mp w.property.2.symm
  obtain ⟨j, hj⟩ := remote_adj_unique_agreement H h z u v w.property.1
  have hij : i = j := (hj i).mp hv.symm
  exact ⟨v, w.property.1, eq_flipExcept_of_agreement (by simpa [← hij] using hj)⟩

private def hasEvenParity (b : Bits) : Prop :=
  [b 0, b 1, b 2, b 3, b 4].foldl Bool.xor false = false

private instance (b : Bits) : Decidable (hasEvenParity b) :=
  inferInstanceAs (Decidable ([b 0, b 1, b 2, b 3, b 4].foldl Bool.xor false = false))

private abbrev EvenBits := {b : Bits // hasEvenParity b}

private theorem evenBits_card : Fintype.card EvenBits = 16 := by decide

private theorem evenBits_generated : ∀ b : EvenBits,
    b.val = (fun _ => false) ∨ (∃ i, b.val = flipExcept i (fun _ => false)) ∨
      ∃ i j, b.val = flipExcept j (flipExcept i (fun _ => false)) := by decide

private theorem remoteCode_surjects (z : Hᶜ.neighborSet r) (b : EvenBits) :
    ∃ u : Hᶜ.neighborSet r, remoteCode H h z u = b.val := by
  obtain hb | ⟨i, hb⟩ | ⟨i, j, hb⟩ := evenBits_generated b
  · exact ⟨z, (remoteCode_zero H h z).trans hb.symm⟩
  · obtain ⟨u, _, hu⟩ := remote_flip_neighbor H h z z i
    exact ⟨u, by rw [hu, remoteCode_zero H h z, hb]⟩
  · obtain ⟨u, _, hu⟩ := remote_flip_neighbor H h z z i
    obtain ⟨v, _, hv⟩ := remote_flip_neighbor H h z u j
    exact ⟨v, by rw [hv, hu, remoteCode_zero H h z, hb]⟩

private noncomputable def remoteChart (z : Hᶜ.neighborSet r) : EvenBits ≃ Hᶜ.neighborSet r := by
  classical
  let f (b : EvenBits) := Classical.choose (remoteCode_surjects H h z b)
  refine Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · intro a b he
    apply Subtype.ext
    have ha : remoteCode H h z (f a) = a.val := Classical.choose_spec (remoteCode_surjects H h z a)
    have hb : remoteCode H h z (f b) = b.val := Classical.choose_spec (remoteCode_surjects H h z b)
    exact ha.symm.trans ((congrArg (remoteCode H h z) he).trans hb)
  · rw [evenBits_card, Hᶜ.card_neighborSet_eq_degree]
    exact (h.compl.regular r).symm

private theorem remoteChart_code (z : Hᶜ.neighborSet r) (b : EvenBits) :
    remoteCode H h z (remoteChart H h z b) = b.val :=
  Classical.choose_spec (remoteCode_surjects H h z b)

private theorem remoteChart_adj (z : Hᶜ.neighborSet r) (b c : EvenBits) :
    H.Adj (remoteChart H h z b).val (remoteChart H h z c).val ↔
      ∃ i, c.val = flipExcept i b.val := by
  let u := remoteChart H h z b
  let v := remoteChart H h z c
  change H.Adj u.val v.val ↔ _
  have hu : remoteCode H h z u = b.val := remoteChart_code H h z b
  have hv : remoteCode H h z v = c.val := remoteChart_code H h z c
  constructor
  · intro huv
    obtain ⟨i, hi⟩ := remote_adj_unique_agreement H h z u v huv
    exact ⟨i, by rw [← hu, ← hv]; exact eq_flipExcept_of_agreement hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨w, huw, hw⟩ := remote_flip_neighbor H h z u i
    have he : w = v := by
      obtain ⟨d, hd⟩ := (remoteChart H h z).surjective w
      have hdc : d = c := by
        apply Subtype.ext
        rw [← remoteChart_code H h z d, hd, hw, hu, hi]
      rw [← hd, hdc]
    exact he ▸ huw

private def splitRoot (r : V) : (H.neighborSet r ⊕ Hᶜ.neighborSet r) ≃ {v : V // v ≠ r} where
  toFun := fun
    | .inl a => ⟨a.val, (H.ne_of_adj a.property).symm⟩
    | .inr b => ⟨b.val, b.property.1.symm⟩
  invFun := fun v => if h : H.Adj r v.val then .inl ⟨v.val, h⟩
    else .inr ⟨v.val, v.property.symm, h⟩
  left_inv := by
    rintro (a | b)
    · have ha : H.Adj r a.val := a.property
      simp [ha]
    · have hb : ¬ H.Adj r b.val := b.property.2
      simp [hb]
  right_inv := by
    intro v
    by_cases h : H.Adj r v.val <;> simp [h]

private abbrev RootLabel := Option ((Fin 5 × Bool) ⊕ EvenBits)

private def rootRelated : RootLabel → RootLabel → Prop
  | none, some (.inl _) | some (.inl _), none => True
  | some (.inl a), some (.inl b) => b = (a.1, !a.2)
  | some (.inl a), some (.inr c) | some (.inr c), some (.inl a) => c.val a.1 = a.2
  | some (.inr c), some (.inr d) => ∃ i, d.val = flipExcept i c.val
  | _, _ => False

private noncomputable def rootChart (z : Hᶜ.neighborSet r) : RootLabel ≃ V := by
  classical
  exact (Equiv.optionCongr ((Equiv.sumCongr (localChart H h z) (remoteChart H h z)).trans
    (splitRoot H r))).trans (Equiv.optionSubtypeNe r)

private theorem rootChart_adj (z : Hᶜ.neighborSet r) (a b : RootLabel) :
    H.Adj (rootChart H h z a) (rootChart H h z b) ↔ rootRelated a b := by
  rcases a with _ | (⟨i, c⟩ | c) <;> rcases b with _ | (⟨j, d⟩ | d)
  · exact ⟨fun ha => H.ne_of_adj ha rfl, False.elim⟩
  · exact ⟨fun _ => trivial, fun _ => (localChart H h z (j, d)).property⟩
  · exact ⟨(remoteChart H h z d).property.2, False.elim⟩
  · exact ⟨fun _ => trivial, fun _ => (localChart H h z (i, c)).property.symm⟩
  · exact localChart_adj H h z i j c d
  · rw [adj_comm]
    exact (remoteCode_adj H h z (remoteChart H h z d) i c).trans (by rw [remoteChart_code, rootRelated])
  · exact ⟨fun ha => (remoteChart H h z c).property.2 ha.symm, False.elim⟩
  · exact (remoteCode_adj H h z (remoteChart H h z c) j d).trans (by rw [remoteChart_code, rootRelated])
  · exact remoteChart_adj H h z c d

include h in
private theorem nonlocal_nonempty (r : V) : Nonempty (Hᶜ.neighborSet r) := by
  classical
  apply Fintype.card_pos_iff.mp
  rw [Hᶜ.card_neighborSet_eq_degree, h.compl.regular]
  decide

end Pairing

/-- The parameters $(27,10,1,5)$ determine the graph. Each root gives five
matched pairs of neighbours. The nonneighbours are labelled by the sixteen
even words on the five pairs, with edges given by changing four positions. -/
theorem schlaefli_complement_unique {V W : Type*} [Fintype V] [Fintype W]
    (H : SimpleGraph V) (K : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hH : H.IsSRGWith 27 10 1 5) (hK : K.IsSRGWith 27 10 1 5) :
    Nonempty (H ≃g K) := by
  classical
  obtain ⟨r⟩ : Nonempty V := Fintype.card_pos_iff.mp (by rw [hH.card]; decide)
  obtain ⟨s⟩ : Nonempty W := Fintype.card_pos_iff.mp (by rw [hK.card]; decide)
  obtain ⟨x⟩ := nonlocal_nonempty H hH r
  obtain ⟨y⟩ := nonlocal_nonempty K hK s
  let eH := rootChart H hH x
  let eK := rootChart K hK y
  refine ⟨⟨eH.symm.trans eK, ?_⟩⟩
  intro a b
  change K.Adj (eK (eH.symm a)) (eK (eH.symm b)) ↔ H.Adj a b
  exact (rootChart_adj K hK y _ _).trans (by
    simpa only [eH, Equiv.apply_symm_apply] using (rootChart_adj H hH x (eH.symm a) (eH.symm b)).symm)

end EPPAIII.Primitive
