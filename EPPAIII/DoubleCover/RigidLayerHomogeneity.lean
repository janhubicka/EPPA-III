import EPPAIII.DoubleCover.TwoPointAction

/-!
# From global fibre-layer rigidity to homogeneity of the base

This completes a crucial implication in the alternative proof of
Lemma 3.3. Given an EPPA embedding into a graph with an invariant pair
system, if an automorphism mapping any bottom vertex to another bottom
vertex must preserve the whole bottom layer, then the base graph is
homogeneous. In particular this applies to the unique-edge / unique-
nonedge exceptional relations of the one-edge and three-edge patterns.

Unlike the informal proof, the construction here explicitly extracts the
permutation induced on the base and checks the full adjacency relation.
-/

namespace EPPAIII.DoubleCover

/-- Finite-graph homogeneity expressed in the same partial-permutation
representation as `IsEPPAEmbedding`. -/
def IsHomogeneousGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (D : Finset V) (p : Equiv.Perm V),
    IsPartialGraphAutomorphism G D p →
      ∃ σ : Equiv.Perm V,
        IsGraphAutomorphism G σ ∧
        ∀ x : V, x ∈ D → σ x = p x

/-- Any EPPA witness whose graph automorphisms must preserve the full
bottom layer whenever they fix its orientation at one vertex would
already make the induced bottom graph homogeneous. -/
theorem homogeneous_of_global_bottom {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hBottom : ∀ (q : Equiv.Perm (Bool × V))
      (hq : IsGraphAutomorphism H q) (σ : Equiv.Perm V),
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) →
      ∀ x0 : V, (q (false,x0)).1 = false →
      ∀ x : V, (q (false,x)).1 = false) :
    IsHomogeneousGraph G := by
  intro D p hpartial
  by_cases hD : D.Nonempty
  · obtain ⟨x0,hx0⟩ := hD
    obtain ⟨q,hq,hExt⟩ := heppa.2 D p hpartial
    obtain ⟨σ,hσ⟩ := hPairs q hq
    have hbot0 : (q (false,x0)).1 = false := by
      have hh := hExt x0 hx0
      change q (false,x0) = (false,p x0) at hh
      exact congrArg Prod.fst hh
    have hAll : ∀ x : V, (q (false,x)).1 = false :=
      hBottom q hq σ hσ x0 hbot0
    have hMap (x : V) : q (false,x) = (false,σ x) :=
      Prod.ext (hAll x) (hσ false x)
    have hInduced (x y : V) :
        G.Adj x y ↔ H.Adj (false,x) (false,y) := heppa.1 x y
    have hAut : IsGraphAutomorphism G σ := by
      intro x y
      calc
        G.Adj x y ↔ H.Adj (false,x) (false,y) := hInduced x y
        _ ↔ H.Adj (q (false,x)) (q (false,y)) := hq _ _
        _ ↔ H.Adj (false,σ x) (false,σ y) := by rw [hMap x, hMap y]
        _ ↔ G.Adj (σ x) (σ y) := (hInduced (σ x) (σ y)).symm
    refine ⟨σ,hAut,?_⟩
    intro x hx
    have hh := hExt x hx
    change q (false,x) = (false,p x) at hh
    have hs : (q (false,x)).2 = p x := congrArg Prod.snd hh
    exact (hσ false x).symm.trans hs
  · refine ⟨Equiv.refl V, ?_, ?_⟩
    · intro x y
      rfl
    · intro x hx
      exact False.elim (hD ⟨x,hx⟩)

/-- The one-edge or three-edge inter-fibre exceptional relation
forces homogeneity of the selected base graph in an EPPA witness.
This is the precise contradiction mechanism for the two non-Taylor
balanced patterns. -/
theorem homogeneous_of_graph_exceptional {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (high : Bool)
    (hOccurs : ∀ x y : V, x ≠ y → ∃ b : Bool,
      if high then ¬ H.Adj (b,x) (b,y) else H.Adj (b,x) (b,y))
    (hSame : ∀ u v : Bool × V, u.2 ≠ v.2 →
      (if high then ¬ H.Adj u v else H.Adj u v) → u.1 = v.1) :
    IsHomogeneousGraph G := by
  apply homogeneous_of_global_bottom G H heppa hPairs
  intro q hq σ hσ x0 hx0 x
  have huniform := graph_uniform_layer_of_exceptional
    H high q σ hq hσ hOccurs hSame x x0
  exact huniform.trans hx0

end EPPAIII.DoubleCover
