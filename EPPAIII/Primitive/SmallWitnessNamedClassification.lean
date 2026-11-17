import EPPAIII.Primitive.SmallWitnessClassification
import EPPAIII.TwoGraphs.TwoGraphOrderFromGardiner

/-! # The icosahedral and Johnson branches of the small-witness classification -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems EPPAIII.CliqueCovers EPPAIII.DoubleCover EPPAIII.TwoGraphs
open SimpleGraph

universe u v
attribute [local instance] Classical.propDecidable

/-- The base consists of a pentagon and the isolated root. Its Taylor
double is the icosahedron in the exact named-model check. -/
abbrev icosahedralTaylorBase := addIsolate (SimpleGraph.cycleGraph 5)

/-- The base consists of the three-by-three rook graph and the isolated
root. Its Taylor double is Johnson J(6,3) in the exact named-model check. -/
abbrev johnsonTaylorBase := addIsolate rookThreeGraph

/-- The concrete finite homogeneity facts independently checked in
`checks/check_named_taylor_models.py`. -/
structure NamedTaylorFiniteChecks : Prop where
  icosahedral : IsHomogeneousTwoGraph icosahedralTaylorBase
  johnson : IsHomogeneousTwoGraph johnsonTaylorBase

/-- The indicated host isomorphism meets each model fibre exactly once
in the prescribed copy. -/
def IsTaylorTransversalCopy {A V W : Type*} (J : SimpleGraph A) (H : SimpleGraph W)
    (e : V ↪ W) : Prop :=
  ∃ ψ : taylorPairGraph J ≃g H, Function.Bijective (fun x => (ψ.symm (e x)).2)

/-- The two concrete Taylor host models, in the indicated orientation. -/
def NamedTaylorHostCases {V W : Type*} (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  IsTaylorTransversalCopy icosahedralTaylorBase H e ∨
    IsTaylorTransversalCopy johnsonTaylorBase H e

/-- The two concrete Taylor host models with their simultaneous complements. -/
def NamedTaylorWitnessCases {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) : Prop :=
  ¬ IsClusterGraph G ∧ ¬ IsCoClusterGraph G ∧
    (NamedTaylorHostCases H e ∨ NamedTaylorHostCases Hᶜ e)

/-- Fixed-embedding classification with the named finite Taylor models. -/
def SmallWitnessNamedModelCases {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  primitiveCases G H e ∨ ImprimitiveHostModels G H e ∨
    ImprimitiveHostModels Gᶜ Hᶜ e ∨ NamedTaylorWitnessCases G H e

private theorem named_taylor_copy_of_descendant
    {A V W : Type*} (J : SimpleGraph A) (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph W)
    (e : V ↪ W) (hModel : IsTaylorWitnessCopy G H e) {r : V}
    (η : J ≃g rootDescendant G r) :
    IsTaylorTransversalCopy (addIsolate J) H e := by
  classical
  obtain ⟨ψ,hFixed,hModel⟩ := hModel
  let original : taylorPairGraph G ≃g H :=
    ⟨ψ, by
      intro a b
      change (pullbackGraph H ψ).Adj a b ↔ (taylorPairGraph G).Adj a b
      rw [hModel]⟩
  have hBottom (x : V) : original.symm (e x) = (false,x) := by
    apply original.injective
    rw [original.apply_symm_apply]
    exact (hFixed x).symm
  refine ⟨(taylorIsoOfDescendant G η).trans original, ?_⟩
  have hMap : (fun x : V => (((taylorIsoOfDescendant G η).trans original).symm (e x)).2) =
      ((addIsolateIsoRootSwitch G η).symm : V → Option A) := by
    funext x
    change ((taylorIsoOfDescendant G η).symm (original.symm (e x))).2 = _
    rw [hBottom, taylorIsoOfDescendant_symm_snd]
  rw [hMap]
  exact (addIsolateIsoRootSwitch G η).symm.bijective

private theorem named_taylor_host_cases_of_copy
    (hGardiner : ∀ {A : Type u} [Fintype A] (G : SimpleGraph A),
      Nonempty A → IsHomogeneousGraph G → GardinerPublishedModels G)
    {V : Type u} {W : Type v} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (H : SimpleGraph W)
    (e : V ↪ W) (hC : ¬ IsClusterGraph G) (hCo : ¬ IsCoClusterGraph G)
    (hHom : IsHomogeneousTwoGraph G) (hModel : IsTaylorWitnessCopy G H e) :
    NamedTaylorHostCases H e := by
  obtain ⟨r,x,y,hrx,hxy,hry,hrxAdj,hxyAdj,hryNot⟩ :=
    (not_cluster_iff_induced_p3 G).mp hC
  obtain ⟨a,b,c,hab,hbc,hac,habNot,hbcNot,hacAdj⟩ :=
    (not_cocluster_iff_induced_cop3 G).mp hCo
  have hOdd : OddBaseTriple G a b c := by
    simp [OddBaseTriple,habNot,hbcNot,hacAdj.symm]
  have hEven : ¬ OddBaseTriple G r x y := by
    have hNot : ¬ G.Adj y r := fun h => hryNot h.symm
    simp [OddBaseTriple,hrxAdj,hxyAdj,hNot]
  rcases homogeneous_two_graph_nontrivial_descendant_of_gardiner G
      (fun J => hGardiner J) hHom ⟨a,b,c,hab,hac,hbc,hOdd⟩
      ⟨r,x,y,hrx,hry,hxy,hEven⟩ r with hCycle | hRook
  · obtain ⟨η⟩ := hCycle
    exact Or.inl (named_taylor_copy_of_descendant _ G H e hModel η)
  · obtain ⟨η⟩ := hRook
    exact Or.inr (named_taylor_copy_of_descendant _ G H e hModel η)

/-- The icosahedral and Johnson models cover every noncluster Taylor branch. -/
theorem namedTaylorWitnessCases_of_nonclusterTaylorWitnessCases
    (hGardiner : ∀ {A : Type u} [Fintype A] (G : SimpleGraph A),
      Nonempty A → IsHomogeneousGraph G → GardinerPublishedModels G)
    {V : Type u} {W : Type v} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (h : NonclusterTaylorWitnessCases G H e) :
    NamedTaylorWitnessCases G H e := by
  refine ⟨h.1,h.2.1,?_⟩
  rcases h.2.2 with ⟨hHom,hCopy⟩ | ⟨hHom,hCopy⟩
  · exact Or.inl (named_taylor_host_cases_of_copy hGardiner G H e h.1 h.2.1 hHom hCopy)
  · have hC : ¬ IsClusterGraph Gᶜ := by
      intro hGC
      apply h.2.1
      intro a b c hab hbc hac hnab hnbc
      exact (hGC a b c ⟨hab,hnab⟩ ⟨hbc,hnbc⟩ hac).2
    have hCo : ¬ IsCoClusterGraph Gᶜ := by
      intro hGC
      apply h.1
      intro a b c hab hbc hac
      by_contra hnac
      exact hGC a b c hab.ne hbc.ne hac (fun h' => h'.2 hab)
        (fun h' => h'.2 hbc) ⟨hac,hnac⟩
    exact Or.inr (@named_taylor_host_cases_of_copy hGardiner V W _ Gᶜ
      (Compl.adjDecidable V G) Hᶜ e hC hCo hHom hCopy)

private theorem eppa_of_taylor_transversal_copy
    {A V W : Type*} [Fintype A] [Fintype V] (J : SimpleGraph A)
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hHom : IsHomogeneousTwoGraph J)
    (hCopy : IsTaylorTransversalCopy J H e) : IsEPPAEmbedding G H e := by
  obtain ⟨ψ,hBij⟩ := hCopy
  let f := e.trans ψ.symm.toEquiv.toEmbedding
  have hF : IsInducedGraphEmbedding G (taylorPairGraph J) f :=
    fun x y => (hInd x y).trans ψ.symm.map_rel_iff.symm
  have hEppa := taylor_eppa_of_induced_transversal G J f hF hHom hBij
  have hEq : f.trans ψ.toEquiv.toEmbedding = e := by
    apply Function.Embedding.ext
    intro x
    exact ψ.apply_symm_apply (e x)
  simpa only [hEq] using eppa_relabel_host G f hEppa ψ

private theorem eppa_of_named_taylor_host_cases
    {V W : Type*} [Fintype V] (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hChecks : NamedTaylorFiniteChecks)
    (h : NamedTaylorHostCases H e) : IsEPPAEmbedding G H e := by
  rcases h with hIcos | hJohnson
  · exact eppa_of_taylor_transversal_copy _ G H e hInd hChecks.icosahedral hIcos
  · exact eppa_of_taylor_transversal_copy _ G H e hInd hChecks.johnson hJohnson

/-- Both named Taylor alternatives give EPPA for the specified copy. -/
theorem eppa_of_namedTaylorWitnessCases {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hChecks : NamedTaylorFiniteChecks)
    (h : NamedTaylorWitnessCases G H e) : IsEPPAEmbedding G H e := by
  rcases h.2.2 with hDirect | hCompl
  · exact eppa_of_named_taylor_host_cases G H e hInd hChecks hDirect
  · have hIndCompl : IsInducedGraphEmbedding Gᶜ Hᶜ e := by
      intro a b
      change (a ≠ b ∧ ¬ G.Adj a b) ↔ (e a ≠ e b ∧ ¬ H.Adj (e a) (e b))
      rw [e.injective.ne_iff, hInd a b]
    simpa only [compl_compl] using eppa_embedding_complement Gᶜ Hᶜ e
      (eppa_of_named_taylor_host_cases Gᶜ Hᶜ e hIndCompl hChecks hCompl)

/-- Named fixed-embedding classification for vertex-transitive hosts
whose order is at most twice that of the chosen graph. -/
theorem smallWitnessNamedModelCases_iff_eppa
    (hPublished : PublishedRankThreeGraphCoverage.{v})
    (hRecognize : PrimitiveRecognitionInputs.{u,v})
    (hOrthogonal : OrthogonalSearchChecks) (hPaley : SmallPaleyExclusions)
    (hFinite : PrimitiveFiniteChecks) (hTaylorChecks : NamedTaylorFiniteChecks)
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : HasTransitiveGraphAutomorphisms H) :
    SmallWitnessNamedModelCases G H e ↔ IsEPPAEmbedding G H e := by
  constructor
  · rintro (hP | hI | hCo | hT)
    · exact eppa_of_smallWitnessModelCases G H e hInd hHalf hFinite (Or.inl hP)
    · exact eppa_of_smallWitnessModelCases G H e hInd hHalf hFinite (Or.inr (Or.inl hI))
    · exact eppa_of_smallWitnessModelCases G H e hInd hHalf hFinite (Or.inr (Or.inr (Or.inl hCo)))
    · exact eppa_of_namedTaylorWitnessCases G H e hInd hTaylorChecks hT
  · intro hEppa
    rcases smallWitnessModelCases_of_eppa hPublished hRecognize hOrthogonal hPaley hFinite
        G H e ⟨hEppa,hTrans,hHalf⟩ with hP | hI | hCo | hT
    · exact Or.inl hP
    · exact Or.inr (Or.inl hI)
    · exact Or.inr (Or.inr (Or.inl hCo))
    · exact Or.inr (Or.inr (Or.inr
        (namedTaylorWitnessCases_of_nonclusterTaylorWitnessCases
          (fun J => hRecognize.gardinerSelected J) G H e hT)))

end EPPAIII.Primitive
