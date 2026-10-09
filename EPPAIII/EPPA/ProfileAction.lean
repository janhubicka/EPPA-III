import EPPAIII.EPPA.Definitions

/-!
# EPPA extensions act equivariantly on neighbourhood profiles

These lemmas justify the central orbit argument in Sections 3.3--3.7:
a total automorphism of the selected induced graph extends to the witness,
preserves its complementary half, and transports each outside vertex's
profile by the prescribed automorphism of the selected graph.

They do not assume that an extending automorphism fixes an individual
complementary clique.
-/

namespace EPPAIII

/-- A total automorphism lifts through an EPPA embedding. -/
theorem eppa_lifts_total {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (h : IsEPPAEmbedding G H e) (p : Equiv.Perm V)
    (hp : IsGraphAutomorphism G p) :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧
      ∀ v : V, q (e v) = e (p v) := by
  classical
  obtain ⟨q, hq, hrestr⟩ :=
    h.2 Finset.univ p (graphAuto_restricts G p hp Finset.univ)
  exact ⟨q, hq, fun v => hrestr v (Finset.mem_univ v)⟩

/-- A lift of a permutation of the selected vertices preserves their
complement (as a set), even though it may move all complementary cliques. -/
theorem lift_preserves_outside {V W : Type*}
    (e : V ↪ W) (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hcompat : ∀ v : V, q (e v) = e (p v))
    (w : W) (hw : w ∉ Set.range e) :
    q w ∉ Set.range e := by
  intro h
  rcases h with ⟨v, hv⟩
  have hh : q (e (p.symm v)) = e v := by
    simpa using hcompat (p.symm v)
  apply hw
  refine ⟨p.symm v, ?_⟩
  exact q.injective (hv.symm.trans hh.symm)

/-- The neighbourhood of an outside vertex in the distinguished copy. -/
def neighbourhoodProfile {V W : Type*}
    (H : SimpleGraph W) (e : V ↪ W) (w : W) : Set V :=
  {v : V | H.Adj w (e v)}

/-- Transport identity for the neighbourhood profiles. -/
theorem profile_equivariant {V W : Type*}
    (H : SimpleGraph W) (e : V ↪ W)
    (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q)
    (hcompat : ∀ v : V, q (e v) = e (p v))
    (w : W) (v : V) :
    v ∈ neighbourhoodProfile H e w ↔
      p v ∈ neighbourhoodProfile H e (q w) := by
  change H.Adj w (e v) ↔ H.Adj (q w) (e (p v))
  simpa [hcompat v] using hq w (e v)

/-- A packaged, axiom-audited version of the orbit-transport input. -/
theorem eppa_profiles_transport {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (h : IsEPPAEmbedding G H e) (p : Equiv.Perm V)
    (hp : IsGraphAutomorphism G p) (w : W)
    (hw : w ∉ Set.range e) :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧
      q w ∉ Set.range e ∧
      ∀ v : V,
        v ∈ neighbourhoodProfile H e w ↔
          p v ∈ neighbourhoodProfile H e (q w) := by
  obtain ⟨q, hq, hcompat⟩ := eppa_lifts_total G H e h p hp
  exact ⟨q, hq, lift_preserves_outside e p q hcompat w hw,
    fun v => profile_equivariant H e p q hq hcompat w v⟩

end EPPAIII
