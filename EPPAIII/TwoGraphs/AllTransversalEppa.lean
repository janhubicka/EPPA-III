import EPPAIII.TwoGraphs.TransversalParity
import EPPAIII.DoubleCover.DeckSwap

/-!
# Every switching representative is an EPPA transversal

A partial automorphism of an arbitrary Taylor transversal preserves
the odd-parity two-graph. By two-graph homogeneity it extends to a
full base automorphism; the latter lifts to an actual Taylor-double
automorphism.

The lift need not agree with the given partial map on the *chosen
sides*. But pair-adjacency preservation forces its Boolean
discrepancy from the chosen sides to be constant on the prescribed
finite domain. Hence either the lift itself or its composition with
the global deck involution extends the partial graph automorphism.
There is no independent switching choice on individual fibres.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

private theorem bool_pair_agreement
    (a b c d : Bool)
    (h : (a = b ↔ c = d)) :
    (a = c ↔ b = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- A Taylor host lift of a two-graph automorphism has uniform
agreement/disagreement with the chosen transversal sides,
provided the base automorphism extends a partial graph
automorphism of that transversal. -/
theorem taylor_lift_choice_agreement_uniform
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V)
    (t : V → Bool)
    (D : Finset V) (p σ : Equiv.Perm V)
    (hp : EPPAIII.IsPartialGraphAutomorphism
      (taylorTransversalGraph G t) D p)
    (hσ : ∀ x ∈ D, σ x = p x)
    (q : Equiv.Perm (Bool × V))
    (hq : EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q)
    (hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) :
    ∀ x ∈ D, ∀ y ∈ D,
      ((q (t x,x)).1 = t (σ x) ↔
       (q (t y,y)).1 = t (σ y)) := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    rfl
  let H := taylorPairGraph G
  let C := taylorTransversalGraph G t
  have hCompare :
      H.Adj (q (t x,x)) (q (t y,y)) ↔
        H.Adj (t (σ x),σ x) (t (σ y),σ y) := by
    calc
      H.Adj (q (t x,x)) (q (t y,y))
          ↔ H.Adj (t x,x) (t y,y) :=
              (hq (t x,x) (t y,y)).symm
      _ ↔ C.Adj x y := Iff.rfl
      _ ↔ C.Adj (p x) (p y) := hp x y hx hy
      _ ↔ H.Adj (t (p x),p x) (t (p y),p y) := Iff.rfl
      _ ↔ H.Adj (t (σ x),σ x) (t (σ y),σ y) := by
        rw [hσ x hx,hσ y hy]
  change
    ((q (t x,x)).2 ≠ (q (t y,y)).2 ∧
      (G.Adj (q (t x,x)).2 (q (t y,y)).2 ↔
        (q (t x,x)).1 = (q (t y,y)).1)) ↔
    (σ x ≠ σ y ∧
      (G.Adj (σ x) (σ y) ↔ t (σ x) = t (σ y))) at hCompare
  rw [hBase (t x) x, hBase (t y) y] at hCompare
  have hσxy : σ x ≠ σ y := σ.injective.ne hxy
  have hEq :
      (G.Adj (σ x) (σ y) ↔
        (q (t x,x)).1 = (q (t y,y)).1) ↔
      (G.Adj (σ x) (σ y) ↔
        t (σ x) = t (σ y)) := by
    simpa [hσxy] using hCompare
  have hBits :
      ((q (t x,x)).1 = (q (t y,y)).1) ↔
        t (σ x) = t (σ y) := by
    classical
    tauto
  exact bool_pair_agreement
    (q (t x,x)).1 (q (t y,y)).1 (t (σ x)) (t (σ y)) hBits

/-- Main switching-class consequence: a Taylor double whose
associated two-graph is homogeneous is an EPPA witness for EVERY
canonical transversal, with the exact designated embedding. -/
theorem homogeneous_two_graph_all_transversals_eppa
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hHomogeneous : IsHomogeneousTwoGraph G)
    (t : V → Bool) :
    EPPAIII.IsEPPAEmbedding
      (taylorTransversalGraph G t) (taylorPairGraph G)
      (taylorTransversalEmbedding t) := by
  classical
  constructor
  · intro x y
    rfl
  · intro D p hp
    obtain ⟨σ,hAut,hExtend⟩ :=
      hHomogeneous D p
        (partial_transversal_preserves_two_graph G t D p hp)
    obtain ⟨q,hq,hBase⟩ :=
      two_graph_automorphism_lifts_to_taylor G σ hAut
    have hUniform :=
      taylor_lift_choice_agreement_uniform
        G t D p σ hp hExtend q hq hBase
    by_cases hNonempty : D.Nonempty
    · obtain ⟨x₀,hx₀⟩ := hNonempty
      by_cases hAnchor : (q (t x₀,x₀)).1 = t (σ x₀)
      · refine ⟨q,hq,?_⟩
        intro x hx
        have hSide :=
          (hUniform x hx x₀ hx₀).mpr hAnchor
        apply Prod.ext
        · change (q (t x,x)).1 = t (p x)
          rw [← hExtend x hx]
          exact hSide
        · change (q (t x,x)).2 = p x
          exact (hBase (t x) x).trans (hExtend x hx)
      · let deck := deckSwap V
        have hDeck : EPPAIII.IsGraphAutomorphism
            (taylorPairGraph G) deck :=
          taylor_deck_graph_automorphism G
        let Q : Equiv.Perm (Bool × V) := q.trans deck
        have hQ : EPPAIII.IsGraphAutomorphism
            (taylorPairGraph G) Q := by
          intro u v
          exact (hq u v).trans (hDeck (q u) (q v))
        refine ⟨Q,hQ,?_⟩
        intro x hx
        have hNot :
            ¬ ((q (t x,x)).1 = t (σ x)) := by
          intro hh
          exact hAnchor ((hUniform x hx x₀ hx₀).mp hh)
        have hFlip :
            !(q (t x,x)).1 = t (σ x) := by
          cases hqbit : (q (t x,x)).1 <;>
            cases htbit : t (σ x) <;> simp_all
        apply Prod.ext
        · change (!(q (t x,x)).1) = t (p x)
          rw [← hExtend x hx]
          exact hFlip
        · change (q (t x,x)).2 = p x
          exact (hBase (t x) x).trans (hExtend x hx)
    · refine ⟨Equiv.refl (Bool × V),?_,?_⟩
      · intro u v
        rfl
      · intro x hx
        exact (hNonempty ⟨x,hx⟩).elim

/-- Full consequent of the one-for-all proposition:
one non-homogeneous EPPA transversal forces all switching
representatives to be EPPA, via the now-complete homogeneity
theorem. The original manuscript remains untouched. -/
theorem taylor_one_eppa_all_switching_transversals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (EPPAIII.CliqueCovers.closedTwinQuotientGraph
      (taylorPairGraph G)).Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (t : V → Bool) :
    EPPAIII.IsEPPAEmbedding
      (taylorTransversalGraph G t) (taylorPairGraph G)
      (taylorTransversalEmbedding t) := by
  exact homogeneous_two_graph_all_transversals_eppa G
    (taylor_eppa_two_graph_homogeneous_all_cases
      G heppa hNonhomogeneous) t

end EPPAIII.TwoGraphs
