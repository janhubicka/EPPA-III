import EPPAIII.Primitive.ConstituentShapeReduction
import EPPAIII.Primitive.TwoCliqueMatchedCover
import EPPAIII.BlockSystems.ImprimitiveGlobalClassification

/-! # Projecting the checked pair alternatives to the constituent cases -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover
open SimpleGraph

private theorem model_comp {V W U : Type*}
    {A : SimpleGraph V} {B : SimpleGraph W} {C : SimpleGraph U}
    (φ : A ≃g B) (h : IsModelUpToComplement B C) :
    IsModelUpToComplement A C := by
  rcases h with h | h
  · obtain ⟨ψ⟩ := h
    exact Or.inl ⟨φ.trans ψ⟩
  · obtain ⟨ψ⟩ := h
    exact Or.inr ⟨φ.trans ψ⟩

private theorem model_compl {V W : Type*}
    {A : SimpleGraph V} {B : SimpleGraph W}
    (h : IsModelUpToComplement A B) : IsModelUpToComplement Aᶜ B := by
  rcases h with h | h
  · obtain ⟨φ⟩ := h
    exact Or.inr ⟨complHostIso φ⟩
  · obtain ⟨φ⟩ := h
    exact Or.inl ⟨by simpa only [compl_compl] using complHostIso φ⟩

theorem Section8ConstituentCases.compl {V : Type*} [Finite V]
    {G : SimpleGraph V} (h : Section8ConstituentCases G) :
    Section8ConstituentCases Gᶜ := by
  rcases h with (⟨s, t, hK⟩ | ⟨s, t, X, Y, hK⟩) | ⟨n, hn, hK⟩ | ⟨q, hq, hp | hp⟩
  · exact Or.inl (Or.inl ⟨s, t, model_compl hK⟩)
  · exact Or.inl (Or.inr ⟨s, t, X, Y, model_compl hK⟩)
  · exact Or.inr (Or.inl ⟨n, hn, model_compl hK⟩)
  · exact Or.inr (Or.inr ⟨q, hq, Or.inr (by simpa only [compl_compl] using hp)⟩)
  · exact Or.inr (Or.inr ⟨q, hq, Or.inl hp⟩)

private def iso_of_comap_eq {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : V ≃ W) (h : H.comap φ = G) : H ≃g G :=
  { toEquiv := φ.symm
    map_rel_iff' := by
      intro a b
      rw [← h]
      change H.Adj (φ (φ.symm a)) (φ (φ.symm b)) ↔ H.Adj a b
      simp only [Equiv.apply_symm_apply] }

private def iso_of_base_copy {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : V ≃ W) (h : CanonicalBaseCopy G H φ) : H ≃g G :=
  (show G ≃g H from ⟨φ, fun {a b} => (h a b).symm⟩).symm

private theorem small_profile_of_degree {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {n d : ℕ} (hcard : Fintype.card V = n) (hdeg : ∀ x, G.degree x = d)
    (hsmall : (n, d) ∈ smallConstituentProfiles) :
    Section8ConstituentCases G := by
  refine Or.inr (Or.inr ⟨(n, d), hsmall, Or.inl ?_⟩)
  refine ⟨Nat.card_eq_fintype_card.trans hcard, fun x => ?_⟩
  rw [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree]
  exact hdeg x

private theorem smallCases_of_iso {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Section8ConstituentCases H) (φ : G ≃g H) : Section8ConstituentCases G := by
  rcases h with (⟨s, t, hK⟩ | ⟨s, t, X, Y, hK⟩) | ⟨n, hn, hK⟩ | ⟨q, hq, hp | hp⟩
  · exact Or.inl (Or.inl ⟨s, t, model_comp φ hK⟩)
  · exact Or.inl (Or.inr ⟨s, t, X, Y, model_comp φ hK⟩)
  · exact Or.inr (Or.inl ⟨n, hn, model_comp φ hK⟩)
  · exact Or.inr (Or.inr ⟨q, hq, Or.inl (hp.of_iso φ)⟩)
  · exact Or.inr (Or.inr ⟨q, hq, Or.inr (hp.of_iso (complHostIso φ))⟩)

set_option maxRecDepth 40000 in
private theorem cycleFive_constituent_case :
    Section8ConstituentCases (cycleGraph 5) :=
  small_profile_of_degree (n := 5) (d := 2) (by decide) (by decide) (by decide)

private theorem rookThree_constituent_case :
    Section8ConstituentCases rookThreeGraph :=
  small_profile_of_degree (n := 9) (d := 4) (by decide) (by decide) (by decide)

private theorem rookFour_constituent_case : Section8ConstituentCases (rookGraph 4) := by
  let : DecidableRel (rookGraph 4).Adj :=
    fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)))
  exact small_profile_of_degree (n := 16) (d := 6) (by decide) (by decide) (by decide)

private theorem clebsch_constituent_case : Section8ConstituentCases clebschGraph :=
  small_profile_of_degree (n := 16) (d := 5) (by decide) (by decide) (by decide)

set_option maxRecDepth 40000 in
private theorem schlafli_constituent_case : Section8ConstituentCases schlafliGraph :=
  small_profile_of_degree (n := 27) (d := 16) (by decide) (by decide) (by decide)

/-- The normalized finite homogeneous classification supplies the shape
or one of the two screened profiles. -/
theorem section8Cases_of_gardiner {W : Type*} [Fintype W]
    {H : SimpleGraph W} (h : GardinerHomogeneousModels H) :
    Section8ConstituentCases H := by
  rcases h with ⟨s, t, _, _, φ, h⟩ | ⟨s, t, _, _, φ, h⟩ | ⟨φ, h⟩ | ⟨φ, h⟩
  · exact Or.inl (Or.inl ⟨s, t, Or.inl ⟨iso_of_base_copy φ h⟩⟩)
  · exact Or.inl (Or.inl ⟨s, t, Or.inr ⟨iso_of_base_copy φ h⟩⟩)
  · exact smallCases_of_iso cycleFive_constituent_case (iso_of_base_copy φ h)
  · exact smallCases_of_iso rookThree_constituent_case (iso_of_base_copy φ h)

/-- The already checked primitive pair list supplies precisely the types
of information needed for a classified smaller constituent. -/
theorem section8Cases_of_primitiveCases {V W : Type*} [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (hGardiner : Nonempty W → ∀ K : SimpleGraph W,
      IsHomogeneousGraph K → GardinerHomogeneousModels K)
    (h : primitiveCases G H e) : Section8ConstituentCases H := by
  classical
  by_cases hW : ¬ Nonempty W
  · let := not_nonempty_iff.mp hW
    let φ : H ≃g cliqueUnion 0 0 :=
      ⟨Equiv.equivOfIsEmpty _ _, fun {x _} => isEmptyElim x⟩
    exact Or.inl (Or.inl ⟨0, 0, Or.inl ⟨φ⟩⟩)
  have project (A : SimpleGraph V) (B : SimpleGraph W) (hB : orientedPrimitiveCases A B e) :
      Section8ConstituentCases B := by
    obtain hHom | ⟨n, hn, φ, _⟩ | ⟨φ, _, _, _⟩ | ⟨φ, _, _, _⟩ | ⟨φ, _, _, _⟩ := hB
    · exact section8Cases_of_gardiner (hGardiner (not_not.mp hW) B hHom)
    · exact Or.inr (Or.inl ⟨n, hn, Or.inl ⟨φ⟩⟩)
    · exact smallCases_of_iso rookFour_constituent_case φ
    · exact smallCases_of_iso clebsch_constituent_case φ
    · exact smallCases_of_iso schlafli_constituent_case φ
  rcases h with h | h
  · exact project G H h
  · simpa only [compl_compl] using (project Gᶜ Hᶜ h).compl

private theorem wagner_constituent_case : Section8ConstituentCases wagnerCanonicalGraph := by
  let : DecidableRel wagnerCanonicalGraph.Adj :=
    fun a b => by
      change Decidable (wagnerCanonicalAdj a b)
      unfold wagnerCanonicalAdj
      infer_instance
  exact small_profile_of_degree (n := 8) (d := 3) (by decide) (by decide) (by decide)

private theorem equalClique_constituent_case {W : Type*} [Finite W]
    {H : SimpleGraph W} {s t : ℕ} {e : (Fin s × Fin t) ↪ W}
    (h : EqualCliqueHostModels s t H e) : Section8ConstituentCases H := by
  rcases h with ⟨φ, X, Y, _, h⟩ | ⟨_, _, φ, _, h⟩
  · exact Or.inl (Or.inr ⟨s, t, X, Y, Or.inl ⟨iso_of_comap_eq φ h⟩⟩)
  · exact smallCases_of_iso wagner_constituent_case (iso_of_comap_eq φ h)

set_option maxRecDepth 40000 in
private theorem cycleFiveSmall_constituent_case {W : Type*} [Fintype W]
    {H : SimpleGraph W} {e : Fin 5 ↪ W}
    (h : CycleFiveSmallHostPatterns H e) : Section8ConstituentCases H := by
  obtain ⟨φ, _, hp⟩ | ⟨φ, _, hp⟩ | ⟨φ, c, _, hp⟩ := h
  · let : DecidableRel cycleFiveDisjointDoubleGraph.Adj :=
      fun a b => inferInstanceAs (Decidable (a.1 = b.1 ∧ (cycleGraph 5).Adj a.2 b.2))
    exact smallCases_of_iso
      (small_profile_of_degree (n := 10) (d := 2) (by decide) (by decide) (by decide))
      (iso_of_comap_eq φ hp)
  · exact smallCases_of_iso
      (small_profile_of_degree (n := 10) (d := 3) (by decide) (by decide) (by decide))
      (iso_of_comap_eq φ hp)
  · apply smallCases_of_iso _ (iso_of_comap_eq φ hp)
    cases c <;> exact
      small_profile_of_degree (n := 10) (d := 4) (by decide) (by decide) (by decide)

set_option maxRecDepth 40000 in
private theorem rookSmall_constituent_case {W : Type*} [Fintype W]
    {H : SimpleGraph W} {e : rookVertex ↪ W}
    (h : RookSmallHostPatterns H e) : Section8ConstituentCases H := by
  obtain ⟨φ, _, hp⟩ | ⟨φ, c, _, hp⟩ | ⟨φ, c, _, hp⟩ := h
  · let : DecidableRel rookDisjointDoubleGraph.Adj :=
      fun a b => inferInstanceAs (Decidable (a.1 = b.1 ∧ rookThreeGraph.Adj a.2 b.2))
    exact smallCases_of_iso
      (small_profile_of_degree (n := 18) (d := 4) (by decide) (by decide) (by decide))
      (iso_of_comap_eq φ hp)
  · apply smallCases_of_iso _ (iso_of_comap_eq φ hp)
    cases c <;> exact
      small_profile_of_degree (n := 18) (d := 5) (by decide) (by decide) (by decide)
  · apply smallCases_of_iso _ (iso_of_comap_eq φ hp)
    cases c <;> exact
      small_profile_of_degree (n := 18) (d := 8) (by decide) (by decide) (by decide)

/-- Proposition 6.17 projects to a constituent shape or one of the
screened small profiles. The unequal-clique case is a matching cover as
a host graph, independently of the choice of the selected half. -/
theorem section8Cases_of_imprimitiveHostModels {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : ImprimitiveHostModels G H e) : Section8ConstituentCases H := by
  rcases h with ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, h⟩ | ⟨_, _, h | h⟩ |
    ⟨_, _, h | h⟩ | ⟨c, φ, _, _, h⟩
  · exact equalClique_constituent_case h
  · simpa only [compl_compl] using (equalClique_constituent_case h).compl
  · exact cycleFiveSmall_constituent_case h
  · simpa only [compl_compl] using (cycleFiveSmall_constituent_case h).compl
  · exact rookSmall_constituent_case h
  · simpa only [compl_compl] using (rookSmall_constituent_case h).compl
  · have h' : H.comap φ = twoCliqueMatchedGraph c true := h
    exact Or.inl (Or.inr ⟨1, Fintype.card V, .matching, false,
      Or.inl ⟨(iso_of_comap_eq φ h').trans (twoCliqueMatchedGraph_iso_matchingCover c)⟩⟩)

/-- Projection of the actual arbitrary-base imprimitive theorem. The
Taylor branch is supplied separately, as in the manuscript's two-graph
classification. -/
theorem section8Cases_of_generalImprimitiveHostModels
    {V W B : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W} {block : W → B}
    (h : GeneralImprimitiveHostModels G H e block)
    (hTaylor : (∃ φ : Bool × V ≃ W,
        (∀ x : V, φ (false, x) = e x) ∧
        ∃ mate : Bool,
          (∀ x : V, H.Adj (φ (false, x)) (φ (true, x)) ↔ mate = true) ∧
          RepresentsPairPattern G (pullbackGraph H φ) taylor) →
      (∀ u v u' v' : W, block u ≠ block v → block u' ≠ block v' →
        (H.Adj u v ↔ H.Adj u' v') →
        ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q u = u' ∧ q v = v') →
      Section8ConstituentCases H) : Section8ConstituentCases H := by
  rcases h with h | h | ⟨hPair, hOrbits⟩
  · exact section8Cases_of_imprimitiveHostModels h
  · simpa only [compl_compl] using (section8Cases_of_imprimitiveHostModels h).compl
  · exact hTaylor hPair hOrbits

end EPPAIII.Primitive
