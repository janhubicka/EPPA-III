import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Induced fibre actions of an EPPA witness

A self-contained group-action interface toward Section 5's lemma on
2-transitivity. The invariant-pair hypothesis is explicit; it is supplied
for Taylor doubles by the separately audited fibre-rigidity argument.

EPPA gives transitivity on ordered base edges and independently on
ordered base nonedges. Non-homogeneity guarantees an induced host
automorphism whose base permutation is *not* a graph automorphism of G.
These are the exact two inputs to the elementary orbit-merging argument.
-/

namespace EPPAIII.DoubleCover

/-- Every pair of ordered selected vertices can be carried to any
other pair of the same graph adjacency type by an induced host action.
The index permutation is extracted from the true host automorphism. -/
theorem eppa_induced_pair_orbit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hType : G.Adj x y ↔ G.Adj u v) :
    ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V),
      IsGraphAutomorphism H q ∧
      (∀ b : Bool, ∀ z : V, (q (b,z)).2 = σ z) ∧
      σ x = u ∧ σ y = v := by
  obtain ⟨q,hq,hx,hy,_,_⟩ :=
    eppa_maps_two_fibres G H heppa hPairs
      x y u v hxy huv hType
  obtain ⟨σ,hσ⟩ := hPairs q hq
  refine ⟨q,σ,hq,hσ,?_,?_⟩
  · have h := congrArg Prod.snd hx
    exact (hσ false x).symm.trans h
  · have h := congrArg Prod.snd hy
    exact (hσ false y).symm.trans h

/-- If *all* base permutations induced by host automorphisms
preserved G, EPPA would already make G homogeneous. Hence for
non-homogeneous G some induced permutation cannot preserve G. -/
theorem induced_action_not_all_graph_automorphisms
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V),
      IsGraphAutomorphism H q ∧
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) ∧
      ¬ IsGraphAutomorphism G σ := by
  classical
  by_contra hNo
  apply hNonhomogeneous
  intro D p hp
  obtain ⟨q,hq,hExtend⟩ := heppa.2 D p hp
  obtain ⟨σ,hσ⟩ := hPairs q hq
  have hσAut : IsGraphAutomorphism G σ := by
    by_contra hNot
    exact hNo ⟨q,σ,hq,hσ,hNot⟩
  refine ⟨σ,hσAut,?_⟩
  intro x hx
  have h := hExtend x hx
  change q (false,x) = (false,p x) at h
  have hImage : (q (false,x)).2 = p x := congrArg Prod.snd h
  exact (hσ false x).symm.trans hImage

/-- In concrete terms, an induced base permutation must move
at least one ordered pair between adjacency types. -/
theorem induced_action_changes_some_pair_type
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
      (x y : V),
      IsGraphAutomorphism H q ∧
      (∀ b : Bool, ∀ z : V, (q (b,z)).2 = σ z) ∧
      ¬ (G.Adj x y ↔ G.Adj (σ x) (σ y)) := by
  classical
  obtain ⟨q,σ,hq,hσ,hNot⟩ :=
    induced_action_not_all_graph_automorphisms
      G H heppa hPairs hNonhomogeneous
  have hFailure : ∃ x y : V,
      ¬ (G.Adj x y ↔ G.Adj (σ x) (σ y)) := by
    by_contra hNo
    push_neg at hNo
    exact hNot hNo
  obtain ⟨x,y,hMismatch⟩ := hFailure
  exact ⟨q,σ,x,y,hq,hσ,hMismatch⟩

end EPPAIII.DoubleCover
