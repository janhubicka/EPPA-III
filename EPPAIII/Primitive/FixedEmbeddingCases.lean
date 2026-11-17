import EPPAIII.Primitive.MinimalCounterexample
import EPPAIII.Primitive.RankThreeCatalog
import EPPAIII.Primitive.Triangular
import EPPAIII.EPPA.HostRelabel

/-!
# Classification cases on actual selected embeddings

The witnesses for an output case act on the ambient host and the actual
image of the selected embedding. A graph isomorphism of selected graphs
alone does not supply a host automorphism conjugating their embeddings.
-/

namespace EPPAIII.Primitive

universe u v

/-- A witness for a selected graph also witnesses each induced selection
inside that graph, by the same host embedding. -/
theorem eppa_induce_selected {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (h : IsEPPAEmbedding G H e) (S : Set V) :
    IsEPPAEmbedding (G.induce S) H ((Function.Embedding.subtype S).trans e) := by
  classical
  constructor
  · intro x y
    exact h.1 x y
  · intro D p hp
    let p' : Equiv.Perm V := Equiv.Perm.ofSubtype p
    let D' := D.image Subtype.val
    have hPartial : IsPartialGraphAutomorphism G D' p' := by
      intro x y hx hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      have hOn (t : S) : p' t = ↑(p t) := Equiv.Perm.ofSubtype_apply_coe p t
      rw [hOn a, hOn b]
      exact hp a b ha hb
    obtain ⟨q, hq, hExt⟩ := h.2 D' p' hPartial
    refine ⟨q, hq, fun x hx => ?_⟩
    have hOn : p' x = ↑(p x) := Equiv.Perm.ofSubtype_apply_coe p x
    change q (e (x : V)) = e (p x : V)
    simpa only [hOn] using hExt x (Finset.mem_image_of_mem Subtype.val hx)

/-- Precompose a witnessing embedding with any finite induced embedding. -/
theorem eppa_precompose_induced {U V W : Type*} [Finite U]
    (A : SimpleGraph U) (G : SimpleGraph V) (H : SimpleGraph W) (f : U ↪ V) (e : V ↪ W)
    (hf : IsInducedGraphEmbedding A G f) (hEppa : IsEPPAEmbedding G H e) :
    IsEPPAEmbedding A H (f.trans e) := by
  classical
  let S := Set.range f
  let φ := Equiv.ofInjective f f.injective
  let := Fintype.ofFinite U
  let := Fintype.ofEquiv U φ
  exact eppa_relabel_base (G.induce S) H _ (eppa_induce_selected G H e hEppa S) φ A hf

/-- Simultaneous complementation closure for classifications of actual pairs. -/
def complementClosedCases (cases : PairClassification.{u, v}) : PairClassification.{u, v} :=
  fun {_ _} G H e => cases G H e ∨ cases Gᶜ Hᶜ e

theorem complementClosedCases_iff (cases : PairClassification.{u, v})
    {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) :
    complementClosedCases cases G H e ↔ complementClosedCases cases Gᶜ Hᶜ e := by
  simp only [complementClosedCases, compl_compl, or_comm]

/-- A selected copy matches a displayed finite figure when a host
isomorphism places all its vertices within a displayed maximal selection. -/
def MatchesPrimitiveFigure {V W F : Type*} (H : SimpleGraph W)
    (e : V ↪ W) (model : SimpleGraph F) (figures : Set (Set F)) : Prop :=
  ∃ (φ : H ≃g model) (S : Set F), S ∈ figures ∧ ∀ x, φ (e x) ∈ S

/-- The corner `R₃ ⊔ K₁` and the stripe `L₄,₂` in `R₄`. -/
def rookFourFigures : Set (Set (Fin 4 × Fin 4)) :=
  {{x | (x.1.val < 3 ∧ x.2.val < 3) ∨ (x.1.val = 3 ∧ x.2.val = 3)},
   {x | x.2.val < 2}}

/-- The triangular case on the specified selected embedding. Its range
gives the actual edge set of the triangle-free graph on `n` points. -/
def TriangularPair {V W : Type*} (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  ∃ (n : ℕ) (_ : 5 ≤ n) (φ : H ≃g triangularGraph (Fin n)),
    TriangleFreeEdges (Set.range fun x => φ (e x))

/-- A witness for each displayed maximal selection proves the forward
map from figure membership to EPPA for each contained actual selection. -/
theorem eppa_of_matchesPrimitiveFigure {V W F : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (model : SimpleGraph F) (figures : Set (Set F))
    (hFig : MatchesPrimitiveFigure H e model figures)
    (hCertificates : ∀ S ∈ figures,
      IsEPPAEmbedding (model.induce S) model (Function.Embedding.subtype S)) :
    IsEPPAEmbedding G H e := by
  obtain ⟨φ, S, hS, hImage⟩ := hFig
  let f : V ↪ S :=
    ⟨fun x => ⟨φ (e x), hImage x⟩, fun _ _ h => e.injective (φ.injective (congrArg Subtype.val h))⟩
  have hInd' : IsInducedGraphEmbedding G (model.induce S) f := by
    intro x y
    exact (hInd x y).trans φ.map_rel_iff.symm
  have hEppa := eppa_precompose_induced G (model.induce S) model f _
    hInd' (hCertificates S hS)
  have hBack := eppa_relabel_host G _ hEppa φ.symm
  have hEq : (f.trans (Function.Embedding.subtype S)).trans φ.symm.toEquiv.toEmbedding = e := by
    ext x
    exact φ.symm_apply_apply (e x)
  rwa [hEq] at hBack

/-- The sufficiency direction for every actual triangular selection in the
classification. The size bound is unnecessary for this direction. -/
theorem eppa_of_triangularPair {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hTriangular : TriangularPair H e) :
    IsEPPAEmbedding G H e := by
  classical
  obtain ⟨n, _, φ, hTriangleFree⟩ := hTriangular
  let S := Set.range fun x => φ (e x)
  let := Fintype.ofFinite S
  exact eppa_of_matchesPrimitiveFigure G H e hInd (triangularGraph (Fin n)) {S}
    ⟨φ, S, rfl, fun x => ⟨x, rfl⟩⟩ (by
      intro T hT
      have hEq : T = S := hT
      subst T
      exact triangularGraph_eppa_induce S hTriangleFree)

/-- A finite search conclusion for one explicit labelled host. The case
predicate concerns the actual selection, hence requires the ambient
graph orbit comparison as well as abstract selected graph isomorphism. -/
def CanonicalFigureClassification {F : Type*} (model : SimpleGraph F)
    (figures : Set (Set F)) : Prop :=
  ∀ S : Set F, Nat.card F ≤ 2 * Nat.card S →
    (IsEPPAEmbedding (model.induce S) model (Function.Embedding.subtype S) ↔
      MatchesPrimitiveFigure model (Function.Embedding.subtype S) model figures)

/-- Change the presentation of a pair to the range of its embedding. -/
theorem eppa_iff_induce_range {V W : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) :
    IsEPPAEmbedding G H e ↔
      IsEPPAEmbedding (H.induce (Set.range e)) H (Function.Embedding.subtype (Set.range e)) := by
  classical
  let S := Set.range e
  let f : V ≃ S := Equiv.ofInjective e e.injective
  let := Fintype.ofFinite V
  let := Fintype.ofEquiv V f
  have hF (x : S) : e (f.symm x) = x := congrArg Subtype.val (f.apply_symm_apply x)
  constructor
  · intro h
    have hEppa := eppa_relabel_base G H e h f.symm (H.induce S) (by
      intro x y
      change H.Adj (↑x) (↑y) ↔ G.Adj (f.symm x) (f.symm y)
      rw [hInd (f.symm x) (f.symm y), hF, hF])
    have hEq : relabelEmbedding e f.symm = Function.Embedding.subtype S := by
      ext x
      exact hF x
    rwa [hEq] at hEppa
  · intro h
    exact eppa_precompose_induced G (H.induce S) H f.toEmbedding _
      (fun x y => hInd x y) h

/-- A complete finite check for the model classifies every fixed
induced embedding into any isomorphic presentation of that host. -/
theorem canonicalFigureClassification_iff_embedding {V W F : Type*} [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInd : IsInducedGraphEmbedding G H e) (hSize : Nat.card W ≤ 2 * Nat.card V)
    (model : SimpleGraph F) (figures : Set (Set F)) (φ : H ≃g model)
    (hCheck : CanonicalFigureClassification model figures) :
    IsEPPAEmbedding G H e ↔ MatchesPrimitiveFigure H e model figures := by
  let f := e.trans φ.toEquiv.toEmbedding
  let S := Set.range f
  have hS : Nat.card F ≤ 2 * Nat.card S := by
    rw [← Nat.card_congr φ.toEquiv, ← Nat.card_congr (Equiv.ofInjective f f.injective)]
    exact hSize
  have hInd' : IsInducedGraphEmbedding G model f := fun a b =>
    (hInd a b).trans φ.map_rel_iff.symm
  have hEither := (eppa_iff_induce_range G model f hInd').trans (hCheck S hS)
  constructor
  · intro h
    obtain ⟨ψ, T, hT, hImage⟩ := hEither.mp (eppa_relabel_host G e h φ)
    exact ⟨φ.trans ψ, T, hT, fun x => hImage ⟨f x, ⟨x, rfl⟩⟩⟩
  · rintro ⟨ψ, T, hT, hImage⟩
    have hMatch : MatchesPrimitiveFigure model (Function.Embedding.subtype S) model figures :=
      ⟨φ.symm.trans ψ, T, hT, fun x => by
        obtain ⟨a, ha⟩ := x.property
        change ψ (φ.symm x.val) ∈ T
        rw [← ha]
        change ψ (φ.symm (φ (e a))) ∈ T
        simpa only [RelIso.symm_apply_apply] using hImage a⟩
    have hBack := eppa_relabel_host G f (hEither.mpr hMatch) φ.symm
    have hEq : f.trans φ.symm.toEquiv.toEmbedding = e := by
      ext x
      exact φ.symm_apply_apply (e x)
    rwa [hEq] at hBack

end EPPAIII.Primitive
