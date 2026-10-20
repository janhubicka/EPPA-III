import EPPAIII.TwoGraphs.TaylorTwinQuotientOccupancy
import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# Vertex transitivity of a Taylor double from EPPA

The proof of Section 5 fibre rigidity begins by observing
that single-vertex partial automorphisms of the selected base
are EPPA-extendible and that the deck involution connects the
two sides. We isolate this statement without assuming
vertex-transitivity or any external classification.
-/

namespace EPPAIII.TwoGraphs

/-- One-point EPPA already makes the selected bottom vertices
one orbit under the actual host automorphism group. -/
theorem eppa_selected_bottom_transitive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (x y : V) :
    ∃ q : Equiv.Perm (Bool × V),
      IsGraphAutomorphism H q ∧
      q (false,x) = (false,y) := by
  classical
  let p : Equiv.Perm V := Equiv.swap x y
  have hPartial :
      IsPartialGraphAutomorphism G ({x} : Finset V) p := by
    intro u v hu hv
    have hux : u = x := by simpa using hu
    have hvx : v = x := by simpa using hv
    subst u
    subst v
    simp
  obtain ⟨q,hq,hExtend⟩ :=
    heppa.2 ({x} : Finset V) p hPartial
  refine ⟨q,hq,?_⟩
  have hh := hExtend x (by simp)
  change q (false,x) = (false,p x) at hh
  simpa [p] using hh

/-- The Taylor deck automorphism supplies the other half of
the host. Consequently every canonical Taylor double which
is an EPPA witness for its bottom graph is vertex-transitive. -/
theorem taylor_double_vertex_transitive_of_eppa
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (heppa : IsEPPAEmbedding G
      (taylorPairGraph G)
      (EPPAIII.DoubleCover.bottomEmbedding V)) :
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (taylorPairGraph G) := by
  intro u v
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  obtain ⟨q,hq,hBottom⟩ :=
    eppa_selected_bottom_transitive
      G (taylorPairGraph G) heppa x y
  let deck := EPPAIII.DoubleCover.deckSwap V
  let p := if b then deck else Equiv.refl (Bool × V)
  let r := if c then deck else Equiv.refl (Bool × V)
  have hDeck := taylor_deck_graph_automorphism G
  have hp : IsGraphAutomorphism (taylorPairGraph G) p := by
    cases b
    · intro a a'
      rfl
    · exact hDeck
  have hr : IsGraphAutomorphism (taylorPairGraph G) r := by
    cases c
    · intro a a'
      rfl
    · exact hDeck
  let σ := (p.trans q).trans r
  have hσ : IsGraphAutomorphism (taylorPairGraph G) σ := by
    intro a a'
    exact (hp a a').trans
      ((hq (p a) (p a')).trans
        (hr (q (p a)) (q (p a'))))
  refine ⟨σ,hσ,?_⟩
  cases b <;> cases c <;>
    simp [σ,p,r,deck,EPPAIII.DoubleCover.deckSwap,hBottom]

end EPPAIII.TwoGraphs
