import EPPAIII.Primitive.TriangularRoot
import EPPAIII.Primitive.TriangularEmbedding
import Mathlib.Tactic.FinCases

/-!
# Abstract triangle-free presentations of large triangular selections

An abstract triangle-free line-graph presentation has no induced diamond. A
root triangle in the given embedding must therefore form an isolated component.
It uses four points in the triangle-free presentation, where it is a star.
Mantel's bound on the remaining points contradicts the half-order hypothesis.
-/

namespace EPPAIII.Primitive

private theorem star_center {V : Type*} [DecidableEq V] {S : Set (TwoSet V)}
    (hS : TriangleFreeEdges S) (a b c : S)
    (hab : ((triangularGraph V).induce S).Adj a b)
    (hac : ((triangularGraph V).induce S).Adj a c)
    (hbc : ((triangularGraph V).induce S).Adj b c) :
    ∃ x : V, x ∈ a.val.val ∧ x ∈ b.val.val ∧ x ∈ c.val.val := by
  classical
  let G := (triangularGraph V).induce S
  have hnab : a ≠ b := G.ne_of_adj hab
  have hnac : a ≠ c := G.ne_of_adj hac
  have hnbc : b ≠ c := G.ne_of_adj hbc
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  let f : Fin 3 ↪ S :=
    ⟨fun i => if i = 0 then a else if i = 1 then b else c, by
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all⟩
  have hf₀ : f 0 = a := rfl
  have hf₁ : f 1 = b := rfl
  have hf₂ : f 2 = c := rfl
  have hAdj (i : Fin 3) (_ : i ∈ Finset.univ) (j : Fin 3) (_ : j ∈ Finset.univ)
      (hij : i ≠ j) : (triangularGraph V).Adj (f i).val (f j).val := by
    change G.Adj (f i) (f j)
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | exact hab
      | exact hac
      | exact hbc
      | exact hba
      | exact hca
      | exact hcb
  obtain ⟨x, hx⟩ := exists_common_point_of_triangularClique hS f
    (by decide : 1 < (Finset.univ : Finset (Fin 3)).card) hAdj
  exact ⟨x, by simpa only [hf₀] using hx 0 (by simp),
    by simpa only [hf₁] using hx 1 (by simp), by simpa only [hf₂] using hx 2 (by simp)⟩

private theorem edges_no_diamond {V : Type*} [DecidableEq V] {S : Set (TwoSet V)}
    (hS : TriangleFreeEdges S) (a b c d : S)
    (hab : ((triangularGraph V).induce S).Adj a b)
    (hac : ((triangularGraph V).induce S).Adj a c)
    (hbc : ((triangularGraph V).induce S).Adj b c)
    (hda : ((triangularGraph V).induce S).Adj d a)
    (hdb : ((triangularGraph V).induce S).Adj d b)
    (hdc : ¬((triangularGraph V).induce S).Adj d c)
    (hdc' : d ≠ c) : False := by
  obtain ⟨x, ha, hb, hc⟩ := star_center hS a b c hab hac hbc
  have hdx : x ∉ d.val.val := fun hx => hdc ⟨fun h => hdc' (Subtype.ext h), x, hx, hc⟩
  obtain ⟨y, hxy, hy⟩ := exists_triangularPair_of_mem ha
  obtain ⟨z, hxz, hz⟩ := exists_triangularPair_of_mem hb
  have hyz : y ≠ z := by
    intro h
    subst z
    exact hab.1 (hy.trans hz.symm)
  have hdY : y ∈ d.val.val := by
    obtain ⟨_, w, hdw, haw⟩ := hda
    have h : w = x ∨ w = y := by simpa [hy, triangularPair] using haw
    rcases h with rfl | rfl
    · exact False.elim (hdx hdw)
    · exact hdw
  have hdZ : z ∈ d.val.val := by
    obtain ⟨_, w, hdw, hbw⟩ := hdb
    have h : w = x ∨ w = z := by simpa [hz, triangularPair] using hbw
    rcases h with rfl | rfl
    · exact False.elim (hdx hdw)
    · exact hdw
  apply hS hxy hxz hyz
  · change triangularPair x y hxy ∈ S
    rw [← hy]
    exact a.property
  · change triangularPair x z hxz ∈ S
    rw [← hz]
    exact b.property
  · change triangularPair y z hyz ∈ S
    rw [← triangularPair_of_mem hdY hdZ hyz]
    exact d.property

set_option maxHeartbeats 600000 in
private theorem card_le_of_isolated_star {V : Type*} [DecidableEq V] [Fintype V]
    {S : Set (TwoSet V)} [Fintype S] (hS : TriangleFreeEdges S)
    (r s t : S) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (x : V) (hr : x ∈ r.val.val) (hs : x ∈ s.val.val) (ht : x ∈ t.val.val)
    (hIso : ∀ u : S, u ≠ r → u ≠ s → u ≠ t →
      ¬((triangularGraph V).induce S).Adj u r ∧
      ¬((triangularGraph V).induce S).Adj u s ∧
      ¬((triangularGraph V).induce S).Adj u t) :
    Fintype.card S ≤ 3 + (Fintype.card V - 4) ^ 2 / 4 := by
  classical
  obtain ⟨a, hxa, ha⟩ := exists_triangularPair_of_mem hr
  obtain ⟨b, hxb, hb⟩ := exists_triangularPair_of_mem hs
  obtain ⟨c, hxc, hc⟩ := exists_triangularPair_of_mem ht
  have hab : a ≠ b := by
    intro h
    subst b
    exact hrs (Subtype.ext (ha.trans hb.symm))
  have hac : a ≠ c := by
    intro h
    subst c
    exact hrt (Subtype.ext (ha.trans hc.symm))
  have hbc : b ≠ c := by
    intro h
    subst c
    exact hst (Subtype.ext (hb.trans hc.symm))
  let points : Finset V := {x, a, b, c}
  have hPoints : points.card = 4 := by
    simp [points, hxa, hxb, hxc, hab, hac, hbc]
  let outside : Set V := (↑points : Set V)ᶜ
  have hOutside : Fintype.card outside = Fintype.card V - 4 := by
    have hCard : Fintype.card outside = (Finset.univ \ points).card :=
      Fintype.card_of_subtype _ (fun v => by simp [outside])
    rw [hCard, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hPoints]
  let removed : Finset (TwoSet V) := {r.val, s.val, t.val}
  have hRemoved : removed.card = 3 :=
    Finset.card_eq_three.mpr ⟨r.val, s.val, t.val, fun h => hrs (Subtype.ext h),
      fun h => hrt (Subtype.ext h), fun h => hst (Subtype.ext h), rfl⟩
  let selected : Set (TwoSet V) := S \ ↑removed
  let G := triangularRootGraph selected
  have hSupport : G.support ⊆ outside := by
    intro v hv
    obtain ⟨w, hw⟩ := G.mem_support.mp hv
    have hvw := hw.ne
    have hMembership : triangularPair v w hvw ∈ selected :=
      (triangularRootGraph_adj selected hvw).mp hw
    let u : S := ⟨triangularPair v w hvw, hMembership.1⟩
    have hur : u ≠ r := by
      intro h
      apply hMembership.2
      change u.val ∈ removed
      simp [h, removed]
    have hus : u ≠ s := by
      intro h
      apply hMembership.2
      change u.val ∈ removed
      simp [h, removed]
    have hut : u ≠ t := by
      intro h
      apply hMembership.2
      change u.val ∈ removed
      simp [h, removed]
    obtain ⟨hnr, hns, hnt⟩ := hIso u hur hus hut
    have hvu : v ∈ u.val.val := by simp [u, triangularPair]
    have hAvoid (p : S) (hne : u ≠ p)
        (hNotAdj : ¬((triangularGraph V).induce S).Adj u p) :
        v ∉ p.val.val :=
      fun hp => hNotAdj ⟨fun h => hne (Subtype.ext h), v, hvu, hp⟩
    have hvr := hAvoid r hur hnr
    have hvs := hAvoid s hus hns
    have hvt := hAvoid t hut hnt
    have hNotPoints : v ∉ points := by
      intro h
      simp only [points, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact hvr hr
      · exact hvr (by simp [ha, triangularPair])
      · exact hvs (by simp [hb, triangularPair])
      · exact hvt (by simp [hc, triangularPair])
    exact hNotPoints
  have hCF : G.CliqueFree 3 := (triangularRootGraph_cliqueFree_iff selected).mpr (by
    intro a' b' c' hab' hac' hbc' h₁ h₂ h₃
    exact hS hab' hac' hbc' h₁.1 h₂.1 h₃.1)
  have hCFinduce : (G.induce outside).CliqueFree 3 :=
    (SimpleGraph.cliqueFree_induce_iff G outside 3).mpr hCF.cliqueFreeOn
  have hMantel := SimpleGraph.CliqueFree.card_edgeFinset_le (r := 2) hCFinduce
  have hEdgeCard : Fintype.card G.edgeSet = Fintype.card selected :=
    Fintype.card_congr (triangularRootGraphEdgeEquiv selected)
  have hIndEdges : Fintype.card (G.induce outside).edgeSet = Fintype.card G.edgeSet := by
    have h := SimpleGraph.card_edgeFinset_induce_of_support_subset
      (G := G) (s := outside) hSupport
    simpa only [SimpleGraph.edgeFinset_card] using h
  rw [SimpleGraph.edgeFinset_card, hIndEdges, hEdgeCard, SimpleGraph.turanNumber_two,
    hOutside] at hMantel
  have hCard := Set.ncard_le_ncard_sdiff_add_ncard S (↑removed : Set (TwoSet V))
  have hRemovedSet : (↑removed : Set (TwoSet V)).ncard = 3 := by simpa using hRemoved
  change S.ncard ≤ selected.ncard + (↑removed : Set (TwoSet V)).ncard at hCard
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card', hRemovedSet] at hCard
  simp only [Set.toFinset_card] at hCard
  omega

/-- A large triangular selection with a triangle-free presentation on the
same number of points is triangle-free in its actual embedding. -/
theorem triangleFreeEdges_of_triangularIso {V : Type*} [Fintype V] [DecidableEq V]
    (S S' : Set (TwoSet V)) [Fintype S] [Fintype S']
    (f : (triangularGraph V).induce S ≃g (triangularGraph V).induce S')
    (hS' : TriangleFreeEdges S') (hV : 5 ≤ Fintype.card V)
    (hLarge : Fintype.card (TwoSet V) ≤ 2 * Fintype.card S) :
    TriangleFreeEdges S := by
  intro a b c hab hac hbc h₁ h₂ h₃
  let r : S := ⟨triangularPair a b hab, h₁⟩
  let s : S := ⟨triangularPair a c hac, h₂⟩
  let t : S := ⟨triangularPair b c hbc, h₃⟩
  obtain ⟨hrs, hrt, hst⟩ := root_pairs_adjacent hab hac hbc
  let G := (triangularGraph V).induce S
  have hrs' : G.Adj r s := hrs
  have hrt' : G.Adj r t := hrt
  have hst' : G.Adj s t := hst
  have rootIsolated (u : S) (hur : u ≠ r) (hus : u ≠ s) (hut : u ≠ t) :
      ¬G.Adj u r ∧ ¬G.Adj u s ∧ ¬G.Adj u t := by
    have huv : u.val ≠ r.val := fun h => hur (Subtype.ext h)
    have huw : u.val ≠ s.val := fun h => hus (Subtype.ext h)
    have hux : u.val ≠ t.val := fun h => hut (Subtype.ext h)
    have noDiamond (e₁ e₂ e₃ : S) (h₁₂ : G.Adj e₁ e₂) (h₁₃ : G.Adj e₁ e₃)
        (h₂₃ : G.Adj e₂ e₃) (h₁' : G.Adj u e₁) (h₂' : G.Adj u e₂)
        (h₃' : ¬G.Adj u e₃) (hNe : u ≠ e₃) : False :=
      edges_no_diamond hS' (f e₁) (f e₂) (f e₃) (f u)
        (f.map_rel_iff.mpr h₁₂) (f.map_rel_iff.mpr h₁₃) (f.map_rel_iff.mpr h₂₃)
        (f.map_rel_iff.mpr h₁') (f.map_rel_iff.mpr h₂')
        (fun h => h₃' (f.map_rel_iff.mp h)) (f.injective.ne hNe)
    have noFourth (har : G.Adj u r) (has : G.Adj u s) (hat : G.Adj u t) : False :=
      no_fourth_for_root_triangle hab hac hbc u.val har has hat
    have ha : a ∉ u.val.val := by
      intro h
      have hUr : G.Adj u r := ⟨huv, a, h, by simp [r, triangularPair]⟩
      have hUs : G.Adj u s := ⟨huw, a, h, by simp [s, triangularPair]⟩
      exact noDiamond r s t hrs' hrt' hst' hUr hUs (noFourth hUr hUs) hut
    have hb : b ∉ u.val.val := by
      intro h
      have hUr : G.Adj u r := ⟨huv, b, h, by simp [r, triangularPair]⟩
      have hUt : G.Adj u t := ⟨hux, b, h, by simp [t, triangularPair]⟩
      exact noDiamond r t s hrt' hrs' hst'.symm hUr hUt
        (fun h => noFourth hUr h hUt) hus
    have hc : c ∉ u.val.val := by
      intro h
      have hUs : G.Adj u s := ⟨huw, c, h, by simp [s, triangularPair]⟩
      have hUt : G.Adj u t := ⟨hux, c, h, by simp [t, triangularPair]⟩
      exact noDiamond s t r hst' hrs'.symm hrt'.symm hUs hUt
        (fun h => noFourth h hUs hUt) hur
    constructor
    · rintro ⟨_, v, hv, hv'⟩
      have h : v = a ∨ v = b := by simpa [r, triangularPair] using hv'
      exact h.elim (fun h => ha (h ▸ hv)) (fun h => hb (h ▸ hv))
    · constructor
      · rintro ⟨_, v, hv, hv'⟩
        have h : v = a ∨ v = c := by simpa [s, triangularPair] using hv'
        exact h.elim (fun h => ha (h ▸ hv)) (fun h => hc (h ▸ hv))
      · rintro ⟨_, v, hv, hv'⟩
        have h : v = b ∨ v = c := by simpa [t, triangularPair] using hv'
        exact h.elim (fun h => hb (h ▸ hv)) (fun h => hc (h ▸ hv))
  obtain ⟨x, hxr, hxs, hxt⟩ := star_center hS' (f r) (f s) (f t)
    (f.map_rel_iff.mpr hrs') (f.map_rel_iff.mpr hrt') (f.map_rel_iff.mpr hst')
  have hIso (u : S') (hur : u ≠ f r) (hus : u ≠ f s) (hut : u ≠ f t) :
      ¬((triangularGraph V).induce S').Adj u (f r) ∧
      ¬((triangularGraph V).induce S').Adj u (f s) ∧
      ¬((triangularGraph V).induce S').Adj u (f t) := by
    obtain ⟨hnr, hns, hnt⟩ := rootIsolated (f.symm u)
      (fun h => hur (by simpa using congrArg f h))
      (fun h => hus (by simpa using congrArg f h))
      (fun h => hut (by simpa using congrArg f h))
    exact ⟨fun h => hnr (f.map_rel_iff.mp (by simpa using h)),
      fun h => hns (f.map_rel_iff.mp (by simpa using h)),
      fun h => hnt (f.map_rel_iff.mp (by simpa using h))⟩
  have hUpper := card_le_of_isolated_star hS' (f r) (f s) (f t)
    (f.injective.ne (G.ne_of_adj hrs')) (f.injective.ne (G.ne_of_adj hrt'))
    (f.injective.ne (G.ne_of_adj hst')) x hxr hxs hxt hIso
  rw [← Fintype.card_congr f.toEquiv] at hUpper
  rw [triangularGraph_card, Nat.choose_two_right] at hLarge
  have hArith : Fintype.card V * (Fintype.card V - 1) ≤
      13 + (Fintype.card V - 4) ^ 2 := by omega
  let k := Fintype.card V - 4
  have hk : 0 < k := by dsimp [k]; omega
  have h4 : Fintype.card V = k + 4 := by dsimp [k]; omega
  have h3 : Fintype.card V - 1 = k + 3 := by omega
  rw [h3, h4] at hArith
  have hSub : k + 4 - 4 = k := by omega
  rw [hSub, pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add] at hArith
  omega

open Sym2

private def triangularSelectionOfGraph {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : Set (TwoSet V) :=
  {p | ∃ e : G.edgeSet, p.val = e.val.toFinset}

private theorem triangularRootGraph_selection {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) : triangularRootGraph (triangularSelectionOfGraph G) = G := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  rw [triangularRootGraph_adj _ hxy]
  constructor
  · rintro ⟨e, he⟩
    have he' : s(x, y).toFinset = e.val.toFinset := Sym2.toFinset_mk_eq.trans he
    have heq : s(x, y) = e.val := Sym2.ext fun z => by
      rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset, he']
    change s(x, y) ∈ G.edgeSet
    rw [heq]
    exact e.property
  · intro h
    exact ⟨⟨s(x, y), h⟩, Sym2.toFinset_mk_eq.symm⟩

/-- The half-order triangular classification in the paper's abstract
line-graph formulation, for any given induced embedding into the host. -/
theorem triangularGraph_eppa_iff_triangleFreeLineGraph {U V : Type*}
    [Fintype U] [Fintype V] [DecidableEq V] (G : SimpleGraph U) (e : U ↪ TwoSet V)
    (hInduced : IsInducedGraphEmbedding G (triangularGraph V) e)
    (hV : 5 ≤ Fintype.card V)
    (hLarge : Fintype.card (TwoSet V) ≤ 2 * Fintype.card U) :
    IsEPPAEmbedding G (triangularGraph V) e ↔
      ∃ K : SimpleGraph V, K.CliqueFree 3 ∧ Nonempty (G ≃g K.lineGraph) := by
  classical
  let S := Set.range e
  let f := Equiv.ofInjective e e.injective
  let : Fintype S := Fintype.ofEquiv U f
  let iso : G ≃g (triangularGraph V).induce S :=
    ⟨f, by intro x y; exact (hInduced x y).symm⟩
  rw [triangularGraph_eppa_iff_triangleFreeRange G e hInduced hV hLarge]
  constructor
  · intro h
    exact ⟨triangularRootGraph S, (triangularRootGraph_cliqueFree_iff S).mpr h,
      ⟨iso.trans (triangularRootGraphLineGraphIso S).symm⟩⟩
  · rintro ⟨K, hK, ⟨hIso⟩⟩
    let S' := triangularSelectionOfGraph K
    let : Fintype S' := Fintype.ofFinite S'
    have hRoot : triangularRootGraph S' = K := triangularRootGraph_selection K
    have hCF : TriangleFreeEdges S' :=
      (triangularRootGraph_cliqueFree_iff S').mp (hRoot.symm ▸ hK)
    let isoK : K.lineGraph ≃g (triangularGraph V).induce S' :=
      hRoot ▸ triangularRootGraphLineGraphIso S'
    have hCard : Fintype.card S = Fintype.card U := Fintype.card_congr f.symm
    exact triangleFreeEdges_of_triangularIso S S'
      (iso.symm.trans (hIso.trans isoK)) hCF hV (hCard.symm ▸ hLarge)

end EPPAIII.Primitive
