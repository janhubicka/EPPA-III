import EPPAIII.CliqueCovers.RegularGraphIndependent
import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# Majority blocks in regular quotient graphs

For a finite regular graph Q, a set of more than half the vertices
cannot be independent unless Q has no edges. Likewise it cannot be
a clique unless Q is complete: apply the independent-set bound to
the regular complement.

This is the graph-theoretic majority step required in Case 1 of
Lemma 3.12 (unequal clique components). It is independent of how
the quotient, invariant block system, or EPPA action is constructed.
-/

namespace EPPAIII.CliqueCovers

/-- In a finite regular graph, a clique occupying strictly more
than half the vertices forces the entire graph to be complete. -/
theorem regular_majority_clique_eq_top {V : Type*}
    [Fintype V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (d : ℕ) (hRegular : Q.IsRegularOfDegree d)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hClique : Q.IsClique (S : Set V)) :
    Q = ⊤ := by
  classical
  let dc : ℕ := Fintype.card V - 1 - d
  have hRegC : Qᶜ.IsRegularOfDegree dc := hRegular.compl
  have hDcZero : dc = 0 := by
    by_contra hNonzero
    have hPositive : 0 < dc := Nat.pos_of_ne_zero hNonzero
    have hIndependent : Qᶜ.IsIndepSet (S : Set V) :=
      (SimpleGraph.isIndepSet_compl Q).mpr hClique
    have hBound :=
      regular_graph_independent_card_le_half
        (Qᶜ) dc hPositive hRegC S hIndependent
    omega
  have hRegZero : Qᶜ.IsRegularOfDegree 0 := by
    simpa only [hDcZero] using hRegC
  have hMaxZero : (Qᶜ).maxDegree = 0 := by
    have hLe : (Qᶜ).maxDegree ≤ 0 :=
      SimpleGraph.maxDegree_le_of_forall_degree_le (G := Qᶜ) 0
        (fun v => by simp [hRegZero v])
    omega
  have hBot : Qᶜ = ⊥ :=
    SimpleGraph.maxDegree_eq_zero_iff.mp hMaxZero
  have hTop := congrArg (fun X : SimpleGraph V => Xᶜ) hBot
  simpa using hTop

/-- In a finite regular graph, an independent set occupying strictly
more than half the vertices forces the graph to be edgeless. -/
theorem regular_majority_independent_eq_bot {V : Type*}
    [Fintype V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (d : ℕ) (hRegular : Q.IsRegularOfDegree d)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hIndependent : Q.IsIndepSet (S : Set V)) :
    Q = ⊥ := by
  classical
  have hRegC : Qᶜ.IsRegularOfDegree
      (Fintype.card V - 1 - d) := hRegular.compl
  have hCliqueC : Qᶜ.IsClique (S : Set V) :=
    (SimpleGraph.isClique_compl Q).mpr hIndependent
  have hTopC : Qᶜ = ⊤ :=
    regular_majority_clique_eq_top (Qᶜ)
      (Fintype.card V - 1 - d) hRegC S hMajority hCliqueC
  have hBot := congrArg (fun X : SimpleGraph V => Xᶜ) hTopC
  simpa using hBot

/-- An induced majority block that is either a clique or an
independent set forces a regular graph to be empty or complete. -/
theorem regular_majority_uniform_block_dichotomy {V : Type*}
    [Fintype V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (d : ℕ) (hRegular : Q.IsRegularOfDegree d)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hUniform : Q.IsClique (S : Set V) ∨
      Q.IsIndepSet (S : Set V)) :
    Q = ⊥ ∨ Q = ⊤ := by
  rcases hUniform with hc | hi
  · exact Or.inr (regular_majority_clique_eq_top
      Q d hRegular S hMajority hc)
  · exact Or.inl (regular_majority_independent_eq_bot
      Q d hRegular S hMajority hi)

/-- Nonempty regular quotient: a majority block on which adjacency
is constant forces all pairs of quotient vertices to be adjacent. -/
theorem regular_majority_uniform_block_nonempty_top {V : Type*}
    [Fintype V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (d : ℕ) (hRegular : Q.IsRegularOfDegree d)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hUniform : Q.IsClique (S : Set V) ∨
      Q.IsIndepSet (S : Set V))
    (hNotEmpty : Q ≠ ⊥) :
    Q = ⊤ := by
  rcases regular_majority_uniform_block_dichotomy
      Q d hRegular S hMajority hUniform with hBot | hTop
  · exact False.elim (hNotEmpty hBot)
  · exact hTop


/-- For a genuinely vertex-transitive quotient graph, regularity is a
conclusion. A nonempty quotient with a majority uniform block is complete. -/
theorem transitive_majority_uniform_block_nonempty_top {V : Type*}
    [Fintype V] [Nonempty V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hTransitive : HasTransitiveGraphAutomorphisms Q)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hUniform : Q.IsClique (S : Set V) ∨
      Q.IsIndepSet (S : Set V))
    (hNotEmpty : Q ≠ ⊥) :
    Q = ⊤ := by
  obtain ⟨d, hRegular⟩ := regular_of_transitive_graph Q hTransitive
  exact regular_majority_uniform_block_nonempty_top
    Q d hRegular S hMajority hUniform hNotEmpty

/-- Ordered-pair transitivity of a set under genuine graph automorphisms
makes the induced quotient relation either complete or empty. -/
theorem pair_transitive_block_uniform {V : Type*}
    (Q : SimpleGraph V) (S : Finset V)
    (hPair : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      ∃ q : Equiv.Perm V,
        EPPAIII.IsGraphAutomorphism Q q ∧ q a = c ∧ q b = d) :
    Q.IsClique (S : Set V) ∨ Q.IsIndepSet (S : Set V) := by
  classical
  by_cases hEdge : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Q.Adj a b
  · left
    intro u hu v hv huv
    obtain ⟨a,ha,b,hb,hab,hAdj⟩ := hEdge
    obtain ⟨q,hq,hqa,hqb⟩ :=
      hPair a ha b hb hab u hu v hv huv
    have hImage : Q.Adj (q a) (q b) := (hq a b).mp hAdj
    simpa only [hqa, hqb] using hImage
  · right
    intro u hu v hv huv
    intro hAdj
    exact hEdge ⟨u,hu,v,hv,huv,hAdj⟩

/-- Abstract end of the occupied-block argument in Claim 3.15:
vertex-transitivity of the quotient, ordered-pair transitivity on
a majority of occupied blocks, and the presence of an inter-block
edge force the quotient to be complete. -/
theorem transitive_majority_pair_action_nonempty_top {V : Type*}
    [Fintype V] [Nonempty V]
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hTransitive : HasTransitiveGraphAutomorphisms Q)
    (S : Finset V) (hMajority : Fintype.card V < 2 * S.card)
    (hPair : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      ∃ q : Equiv.Perm V,
        EPPAIII.IsGraphAutomorphism Q q ∧ q a = c ∧ q b = d)
    (hNotEmpty : Q ≠ ⊥) :
    Q = ⊤ := by
  have hUniform : Q.IsClique (S : Set V) ∨
      Q.IsIndepSet (S : Set V) :=
    pair_transitive_block_uniform Q S hPair
  exact transitive_majority_uniform_block_nonempty_top
    Q hTransitive S hMajority hUniform hNotEmpty

end EPPAIII.CliqueCovers
