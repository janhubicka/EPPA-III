import EPPAIII.Primitive.ConstituentClassifiedModels
import EPPAIII.TwoGraphs.TrivialTwoGraph
import Mathlib.Data.Fintype.Card

/-! # The arbitrary-base Taylor branch of the Section 8 reduction -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover
open EPPAIII.TwoGraphs
open SimpleGraph

/-- The numerical consequence of the published homogeneous two-graph
classification. Both distinct-triple parities occur in the nontrivial case. -/
def HomogeneousTwoGraphOrderRecognition (V : Type*) [Fintype V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj], IsHomogeneousTwoGraph G →
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ EvenTriple G a b c) →
    (∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ OddBaseTriple G a b c) →
    Fintype.card V = 6 ∨ Fintype.card V = 10

private theorem taylor_nontrivial_orders {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hOrder : HomogeneousTwoGraphOrderRecognition V)
    (hHom : IsHomogeneousTwoGraph G) (hC : ¬ IsClusterGraph G) (hCo : ¬ IsCoClusterGraph G) :
    Fintype.card V = 6 ∨ Fintype.card V = 10 := by
  apply hOrder G hHom
  · unfold IsClusterGraph at hC
    push Not at hC
    obtain ⟨a,b,c,hab,hbc,hac,hno⟩ := hC
    exact ⟨a,b,c,hab.ne,hac,hbc.ne,by simp [EvenTriple, hab, hbc, hno]⟩
  · unfold IsCoClusterGraph at hCo
    push Not at hCo
    obtain ⟨a,b,c,hab,hbc,hac,hnab,hnbc,hacAdj⟩ := hCo
    exact ⟨a,b,c,hab,hac,hbc,by
      apply Classical.byContradiction
      intro hn
      have hEven := (even_triple_iff_not_odd G a b c).mpr hn
      simp [EvenTriple, hnab, hnbc, hacAdj] at hEven⟩

private theorem taylor_half_profile {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    HasRegularProfile (taylorPairGraph G) (2 * Fintype.card V, Fintype.card V - 1) := by
  classical
  constructor
  · simp [Nat.card_eq_fintype_card]
  · intro root
    let f (x : V) : Bool := if G.Adj root.2 x then root.1 else !root.1
    have hAdj (x : V) (hx : x ≠ root.2) :
        (taylorPairGraph G).Adj root (f x, x) := by
      change root.2 ≠ x ∧ (G.Adj root.2 x ↔ root.1 = f x)
      refine ⟨hx.symm, ?_⟩
      by_cases h : G.Adj root.2 x <;> cases hr : root.1 <;> simp [f, h, hr]
    let E : (taylorPairGraph G).neighborSet root ≃ {x : V // x ≠ root.2} :=
      { toFun := fun p => ⟨p.val.2, ((show taylorPairAdj G root p.val from p.property).1).symm⟩
        invFun := fun x => ⟨(f x.val, x.val), hAdj x.val x.property⟩
        left_inv := by
          intro p
          apply Subtype.ext
          change (f p.val.2, p.val.2) = p.val
          apply Prod.ext
          swap
          · rfl
          have hp := (show taylorPairAdj G root p.val from p.property).2
          by_cases h : G.Adj root.2 p.val.2
          · simpa [f,h] using hp.mp h
          · have he : root.1 ≠ p.val.1 := fun he => h (hp.mpr he)
            cases hr : root.1 <;> cases hb : p.val.1 <;> simp_all [f]
        right_inv := fun _ => rfl }
    rw [Nat.card_congr E, Nat.card_eq_fintype_card]
    simp

private theorem taylor_order_profile {V : Type*} [Fintype V]
    (G : SimpleGraph V) (h : Fintype.card V = 6 ∨ Fintype.card V = 10) :
    HasScreenedSmallProfile (taylorPairGraph G) := by
  rcases h with h | h
  · exact ⟨(12, 5), by decide, Or.inl (by simpa [h] using taylor_half_profile G)⟩
  · exact ⟨(20, 9), by decide, Or.inl (by simpa [h] using taylor_half_profile G)⟩

private theorem canonical_taylor_eq {V : Type*}
    (G : SimpleGraph V) (P : SimpleGraph (Bool × V))
    (hBottom : IsInducedGraphEmbedding G P (bottomEmbedding V))
    (mate : Bool)
    (hMate : ∀ x : V, P.Adj (false,x) (true,x) ↔ mate = true)
    (hInter : RepresentsPairPattern G P taylor) :
    P = if mate then (taylorPairGraph Gᶜ)ᶜ else taylorPairGraph G := by
  classical
  ext u v
  rcases u with ⟨a,x⟩
  rcases v with ⟨b,y⟩
  by_cases hxy : x = y
  · subst y
    cases mate <;> cases a <;> cases b <;>
      simp [taylorPairGraph, taylorPairAdj, hMate, SimpleGraph.adj_comm P (true,x) (false,x)]
  · have hRev : y ≠ x := Ne.symm hxy
    have hBot : G.Adj x y ↔ P.Adj (false,x) (false,y) := hBottom x y
    by_cases hG : G.Adj x y
    · have ⟨h01,h10,h11⟩ := hInter.1 x y hxy hG
      cases mate <;> cases a <;> cases b <;>
        simp_all [taylor, taylorPairGraph, taylorPairAdj, Prod.ext_iff]
    · have ⟨h01,h10,h11⟩ := hInter.2 x y hxy hG
      cases mate <;> cases a <;> cases b <;>
        simp_all [taylor, taylorPairGraph, taylorPairAdj, Prod.ext_iff]

private theorem taylor_product_has_profile {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {P : SimpleGraph (Bool × V)}
    (heppa : IsEPPAEmbedding G P (bottomEmbedding V))
    (hNonhom : ¬ IsHomogeneousGraph G)
    (hC : ¬ IsClusterGraph G) (hCo : ¬ IsCoClusterGraph G)
    (hRecognition : HomogeneousTwoGraphOrderRecognition V)
    (mate : Bool)
    (hMate : ∀ x : V, P.Adj (false,x) (true,x) ↔ mate = true)
    (hInter : RepresentsPairPattern G P taylor) :
    HasScreenedSmallProfile P := by
  classical
  have hP := canonical_taylor_eq G P heppa.1 mate hMate hInter
  cases mate
  · change P = taylorPairGraph G at hP
    subst P
    have hHom : IsHomogeneousTwoGraph G :=
      taylor_eppa_two_graph_homogeneous_all_cases G heppa hNonhom
    exact taylor_order_profile G (taylor_nontrivial_orders G hRecognition hHom hC hCo)
  · change P = (taylorPairGraph Gᶜ)ᶜ at hP
    subst P
    have hE : IsEPPAEmbedding Gᶜ (taylorPairGraph Gᶜ) (bottomEmbedding V) := by
      simpa using eppa_embedding_complement G (taylorPairGraph Gᶜ)ᶜ (bottomEmbedding V) heppa
    have hHom : IsHomogeneousTwoGraph Gᶜ :=
      taylor_eppa_two_graph_homogeneous_all_cases Gᶜ hE
        ((nonhomogeneous_complement_iff G).mp hNonhom)
    have hCc : ¬ IsClusterGraph Gᶜ := by
      intro hc
      apply hCo
      intro a b c hab hbc hac hnab hnbc
      exact (hc a b c ⟨hab,hnab⟩ ⟨hbc,hnbc⟩ hac).2
    have hCoc : ¬ IsCoClusterGraph Gᶜ := by
      intro hc
      apply hC
      intro a b c hab hbc hac
      exact Classical.byContradiction (fun hnac =>
        hc a b c hab.ne hbc.ne hac (fun h => h.2 hab) (fun h => h.2 hbc) ⟨hac, hnac⟩)
    obtain ⟨p,hp,hreg | hreg⟩ := taylor_order_profile Gᶜ
      (taylor_nontrivial_orders Gᶜ hRecognition hHom hCc hCoc)
    · exact ⟨p,hp,Or.inr (by simpa using hreg)⟩
    · exact ⟨p,hp,Or.inl hreg⟩

/-- The canonical Taylor-pair conclusion projects to one of the two
screened profiles, for the actual selected embedding and either mate bit. -/
theorem screened_profile_of_taylor_pair {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hNonhom : ¬ IsHomogeneousGraph G)
    (hC : ¬ IsClusterGraph G) (hCo : ¬ IsCoClusterGraph G)
    (hRecognition : HomogeneousTwoGraphOrderRecognition V)
    (φ : Bool × V ≃ W) (hBottom : ∀ x : V, φ (false,x) = e x)
    (mate : Bool) (hMate : ∀ x : V, H.Adj (φ (false,x)) (φ (true,x)) ↔ mate = true)
    (hInter : RepresentsPairPattern G (pullbackGraph H φ) taylor) :
    HasScreenedSmallProfile H := by
  let E : pullbackGraph H φ ≃g H := ⟨φ, Iff.rfl⟩
  obtain ⟨p,hp,hreg | hreg⟩ := taylor_product_has_profile G
    (eppa_pullback_bottom G H e heppa φ hBottom) hNonhom hC hCo
    hRecognition mate hMate hInter
  · exact ⟨p,hp,Or.inl (hreg.of_iso E.symm)⟩
  · exact ⟨p,hp,Or.inr (hreg.of_iso (complHostIso E.symm))⟩


/-- The imprimitive case required by smaller-pair induction, including
the arbitrary-base Taylor branch. The published inputs concern finite
homogeneous graphs and the orders of nontrivial homogeneous two-graphs. -/
theorem section8Cases_of_imprimitive_eppa
    {V W B : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block) (hTrans : IsVertexTransitive H)
    (hNonhomogeneousH : ¬ IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤ ((Finset.univ : Finset W).filter
      (fun w => block w = b₀)).card)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hGardiner : IsHomogeneousGraph G → GardinerPublishedModels G)
    (hRecognition : HomogeneousTwoGraphOrderRecognition V) :
    Section8ConstituentCases H := by
  classical
  by_cases hClass : IsHomogeneousGraph G ∨ IsClusterGraph G
  · exact section8Cases_of_imprimitiveHostModels
      (imprimitive_actual_host_classification_from_published_gardiner
        G H e heppa block hBlocks hSurj hTrans hNonhomogeneousH
        hManyBlocks hNontrivial hBound hClass hGardiner).2
  have hNonhom : ¬ IsHomogeneousGraph G := fun h => hClass (Or.inl h)
  by_cases hCo : IsCoClusterGraph G
  · have hClusterC : IsClusterGraph Gᶜ := by
      intro a b c hab hbc hac
      exact ⟨hac,hCo a b c hab.1 hbc.1 hac hab.2 hbc.2⟩
    have hBlocksc : InvariantBlockMap Hᶜ block := by
      intro q hq x y
      have hOrig : IsGraphAutomorphism H q := by
        simpa using graphAutomorphism_complement Hᶜ q hq
      exact hBlocks q hOrig x y
    have hCases := imprimitive_actual_host_classification_from_published_gardiner
      Gᶜ Hᶜ e (eppa_embedding_complement G H e heppa) block hBlocksc hSurj
      (transitive_complement H hTrans) ((nonhomogeneous_complement_iff H).mp hNonhomogeneousH)
      hManyBlocks hNontrivial hBound (Or.inr hClusterC)
      (fun h => (((nonhomogeneous_complement_iff G).mp hNonhom) h).elim)
    simpa only [compl_compl] using (section8Cases_of_imprimitiveHostModels hCases.2).compl
  · have hNoncluster : ¬ IsClusterGraph G := fun h => hClass (Or.inr h)
    have hDouble := nonhomogeneous_imprimitive_eppa_host_exactly_double
      G H e heppa block hBlocks hSurj hTrans hNonhomogeneousH
      hManyBlocks hNontrivial hBound
    obtain ⟨φ,hBottom,mate,hMate,hInter⟩ := transitive_eppa_double_cover_up_to_mate
      G H e heppa block hTrans hBlocks hSurj hNonhom hNoncluster hCo
      hManyBlocks hNontrivial hDouble
    exact Or.inr (Or.inr (screened_profile_of_taylor_pair G H e heppa hNonhom hNoncluster
      hCo hRecognition φ hBottom mate hMate hInter))


/-- Project classified smaller pairs while using the actual EPPA, size, and
transitivity hypotheses in the imprimitive branch. Nonprimitivity supplies
the finite quotient of an invariant equivalence relation. -/
theorem section8Cases_of_primitive_or_imprimitive
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hPair : SmallEPPAPair G H e)
    (hCase : primitiveCases G H e ∨ ¬ IsPrimitiveAutAction H)
    (hGardinerG : Nonempty V → IsHomogeneousGraph G → GardinerPublishedModels G)
    (hGardinerH : Nonempty W → ∀ K : SimpleGraph W,
      IsHomogeneousGraph K → GardinerHomogeneousModels K)
    (hRecognition : HomogeneousTwoGraphOrderRecognition V) :
    Section8ConstituentCases H := by
  classical
  rcases hCase with hPrimitive | hImprimitive
  · exact section8Cases_of_primitiveCases hGardinerH hPrimitive
  by_cases hHom : IsHomogeneousGraph H
  · exact section8Cases_of_primitiveCases (G := G) (e := e) hGardinerH
      (Or.inl (Or.inl hHom))
  unfold IsPrimitiveAutAction at hImprimitive
  push Not at hImprimitive
  obtain ⟨R,hEq,hInv,⟨a,b,hab,hne⟩,⟨c,d,hcd⟩⟩ := hImprimitive
  let S : Setoid W := ⟨R,hEq⟩
  let B := Quotient S
  let : Fintype B := Fintype.ofFinite B
  let block : W → B := Quotient.mk S
  have hBlock (x y : W) : block x = block y ↔ R x y :=
    ⟨@Quotient.exact W S x y, @Quotient.sound W S x y⟩
  have hBlocks : InvariantBlockMap H block := by
    intro q hq x y
    exact (hBlock x y).trans ((hInv q hq x y).trans (hBlock (q x) (q y)).symm)
  have hSurj : Function.Surjective block := fun c => Quotient.inductionOn c (fun x => ⟨x,rfl⟩)
  have hMany : 2 ≤ Fintype.card B :=
    Fintype.one_lt_card_iff.mpr ⟨block c,block d,fun heq => hcd ((hBlock c d).mp heq)⟩
  have hNontrivial : ∃ b₀ : B, 2 ≤ ((Finset.univ : Finset W).filter
      (fun w => block w = b₀)).card := by
    refine ⟨block b, Finset.one_lt_card_iff.mpr ?_⟩
    exact ⟨a,b,by simp [(hBlock a b).mpr hab],by simp,hne⟩
  have hSize : Fintype.card W ≤ 2 * Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using hPair.halfOrder
  have hHostPositive : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨a⟩
  have hSelected : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact section8Cases_of_imprimitive_eppa G H e hPair.eppa block hBlocks hSurj
    hPair.transitive hHom hMany hNontrivial hSize (hGardinerG hSelected) hRecognition

end EPPAIII.Primitive
