import EPPAIII.DoubleCover.DeckSwap

/-!
# Ordered inter-fibre edge and nonedge transitivity

The final assertion of Lemma 3.3 follows from two verified facts:
(1) the induced action of actual host automorphisms on the fibres
    is 2-transitive for a non-homogeneous base (FibreOrbits);
(2) the Taylor pattern has exactly two vertex-pairs of each
    edge/nonedge status above any ordered pair of distinct fibres,
    and the global deck automorphism interchanges them (DeckSwap).

The resulting theorem is intentionally stronger: any two ordered
pairs of vertices from distinct fibres with the *same adjacency
status* are conjugate under a graph automorphism of the host.
-/

namespace EPPAIII.DoubleCover

/-- The missing ordered-edge/nonedge orbit assertion of Lemma 3.3,
expressed directly for a graph in its canonical two-layer coordinates.
There is no assumption of a coherent family of EPPA extensions. -/
theorem eppa_interfibre_pair_status_transitive {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (b c d e : Bool) (x y z w : V)
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hStatus : H.Adj (b,x) (c,y) ↔ H.Adj (d,z) (e,w)) :
    ∃ q : Equiv.Perm (Bool × V),
      IsGraphAutomorphism H q ∧
      q (b,x) = (d,z) ∧ q (c,y) = (e,w) := by
  classical
  obtain ⟨_, _, hTaylor⟩ :=
    eppa_taylor_double_up_to_mate G H heppa hPairs hNonHomogeneous
  obtain ⟨q,σ,hq,hσ,hxz,hyw⟩ :=
    eppa_fibre_action_two_transitive G H heppa hPairs
      hNonHomogeneous x y z w hxy hzw
  let bq : Bool := (q (b,x)).1
  let cq : Bool := (q (c,y)).1
  have hq1 : q (b,x) = (bq,z) :=
    Prod.ext rfl ((hσ b x).trans hxz)
  have hq2 : q (c,y) = (cq,w) :=
    Prod.ext rfl ((hσ c y).trans hyw)
  have hStatus' :
      H.Adj (bq,z) (cq,w) ↔ H.Adj (d,z) (e,w) := by
    calc
      H.Adj (bq,z) (cq,w) ↔
        H.Adj (q (b,x)) (q (c,y)) := by rw [hq1, hq2]
      _ ↔ H.Adj (b,x) (c,y) := (hq (b,x) (c,y)).symm
      _ ↔ H.Adj (d,z) (e,w) := hStatus
  have hChoice :=
    taylor_pair_same_status_eq_or_deck
      G H heppa.1 hTaylor z w hzw bq cq d e hStatus'
  rcases hChoice with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · refine ⟨q,hq,?_,?_⟩
    · apply Prod.ext
      · exact hb
      · exact (hσ b x).trans hxz
    · apply Prod.ext
      · exact hc
      · exact (hσ c y).trans hyw
  · let deck := deckSwap V
    have hDeck : IsGraphAutomorphism H deck :=
      deckSwap_graph_automorphism G H heppa.1 hTaylor
    refine ⟨q.trans deck, ?_, ?_, ?_⟩
    · intro u v
      exact (hq u v).trans (hDeck (q u) (q v))
    · change (!(q (b,x)).1, (q (b,x)).2) = (d,z)
      apply Prod.ext
      · change !bq = d
        rw [hb]
        cases d <;> rfl
      · exact (hσ b x).trans hxz
    · change (!(q (c,y)).1, (q (c,y)).2) = (e,w)
      apply Prod.ext
      · change !cq = e
        rw [hc]
        cases e <;> rfl
      · exact (hσ c y).trans hyw

/-- Transitivity of the host automorphism group on ordered
edges joining different invariant two-point blocks. -/
theorem eppa_interfibre_ordered_edges_transitive {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (b c d e : Bool) (x y z w : V)
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hFirst : H.Adj (b,x) (c,y))
    (hSecond : H.Adj (d,z) (e,w)) :
    ∃ q : Equiv.Perm (Bool × V),
      IsGraphAutomorphism H q ∧
      q (b,x) = (d,z) ∧ q (c,y) = (e,w) := by
  exact eppa_interfibre_pair_status_transitive
    G H heppa hPairs hNonHomogeneous
    b c d e x y z w hxy hzw
    ⟨fun _ => hSecond, fun _ => hFirst⟩

/-- The analogous ordered transitivity on nonedges joining
different invariant two-point blocks. -/
theorem eppa_interfibre_ordered_nonedges_transitive {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (b c d e : Bool) (x y z w : V)
    (hxy : x ≠ y) (hzw : z ≠ w)
    (hFirst : ¬ H.Adj (b,x) (c,y))
    (hSecond : ¬ H.Adj (d,z) (e,w)) :
    ∃ q : Equiv.Perm (Bool × V),
      IsGraphAutomorphism H q ∧
      q (b,x) = (d,z) ∧ q (c,y) = (e,w) := by
  exact eppa_interfibre_pair_status_transitive
    G H heppa hPairs hNonHomogeneous
    b c d e x y z w hxy hzw
    ⟨fun h => False.elim (hFirst h),
     fun h => False.elim (hSecond h)⟩

end EPPAIII.DoubleCover
