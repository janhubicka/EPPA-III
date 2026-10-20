import EPPAIII.TwoGraphs.TaylorTwinQuotientOccupancy
import EPPAIII.CliqueCovers.NonclusterQuotient
import EPPAIII.CliqueCovers.RegularGraphIndependent
import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# Positive-degree regular quotient from one even Taylor triple

In the true-twin quotient proof of Section 5 it is unnecessary
to compute the exact quotient degree m-1. The presence of one
even base triple gives an induced nontransitive-adjacency path
in the Taylor graph, hence its true-twin quotient has an edge.
Vertex transitivity of the Taylor host then gives positive-degree
regularity of the quotient.

This directly supplies the half-order bound on any occupied
independent quotient classes. No deck involution parity or
prelabelled quotient decomposition is assumed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- One even-parity triple generates an induced three-vertex
path in the Taylor double. Consequently it is not a cluster
graph (a disjoint union of cliques). -/
theorem taylor_even_triple_forces_noncluster
    {V : Type*} (G : SimpleGraph V)
    (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hEven : EvenTriple G x y z) :
    ¬ EPPAIII.BlockSystems.IsClusterGraph (taylorPairGraph G) := by
  classical
  let c : Bool := if G.Adj x y then true else false
  have hNonadj :
      ¬ (taylorPairGraph G).Adj (false,x) (c,y) := by
    intro h
    have hRel : G.Adj x y ↔ false = c := h.2
    by_cases hEdge : G.Adj x y
    · simp [c, hEdge] at hRel
    · simp [c, hEdge] at hRel
  obtain ⟨d,hxzAdj,hyzAdj⟩ :=
    taylor_different_fibres_two_step G x y z
      false c hxy hxz hyz hEven hNonadj
  intro hCluster
  have hNe : (false,x) ≠ (c,y) := by
    intro heq
    exact hxy (congrArg Prod.snd heq)
  have hAdj : (taylorPairGraph G).Adj (false,x) (c,y) :=
    hCluster (false,x) (d,z) (c,y)
      hxzAdj hyzAdj.symm hNe
  exact hNonadj hAdj

/-- If a canonical Taylor double has an even base triple,
then its true-twin quotient has a genuine edge. -/
theorem taylor_even_triple_quotient_has_edge
    {V : Type*} (G : SimpleGraph V)
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EvenTriple G x y z) :
    ∃ a b : ClosedTwinQuotient (taylorPairGraph G),
      (closedTwinQuotientGraph (taylorPairGraph G)).Adj a b := by
  obtain ⟨x,y,z,hxy,hxz,hyz,hParity⟩ := hEven
  exact noncluster_twin_quotient_has_edge
    (taylorPairGraph G)
    (taylor_even_triple_forces_noncluster
      G x y z hxy hxz hyz hParity)

/-- A vertex-transitive Taylor double with an even base triple
has a true-twin quotient of *strictly positive* regular degree.
The exact numerical value of the degree is irrelevant. -/
theorem taylor_quotient_positive_regular
    {V : Type*} (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (hTrans : HasTransitiveGraphAutomorphisms (taylorPairGraph G))
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EvenTriple G x y z) :
    ∃ d : ℕ, 0 < d ∧
      (closedTwinQuotientGraph (taylorPairGraph G)).IsRegularOfDegree d := by
  classical
  let H := taylorPairGraph G
  let Q := closedTwinQuotientGraph H
  obtain ⟨a,b,hEdge⟩ :=
    taylor_even_triple_quotient_has_edge G hEven
  letI : Nonempty (ClosedTwinQuotient H) := ⟨a⟩
  obtain ⟨d,hRegular⟩ :=
    regular_of_transitive_graph Q
      (closedTwinQuotient_transitive H hTrans)
  have hNeighbor : b ∈ Q.neighborFinset a := by
    simpa [Q] using hEdge
  have hDegree : 0 < Q.degree a := by
    change 0 < (Q.neighborFinset a).card
    exact Finset.card_pos.mpr ⟨b,hNeighbor⟩
  have hd : 0 < d := by
    rw [hRegular a] at hDegree
    exact hDegree
  exact ⟨d,hd,hRegular⟩

/-- In the first quotient case, if EPPA forces every selected
edge to lie inside a true-twin class, the selected classes occupy
at most half the quotient. -/
theorem taylor_selected_quotient_independent_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G
      (taylorPairGraph G) (EPPAIII.DoubleCover.bottomEmbedding V))
    (hTrans : HasTransitiveGraphAutomorphisms (taylorPairGraph G))
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      EvenTriple G x y z)
    (x y : V) (hXY : G.Adj x y)
    (hTwin : SameClosedNeighbourhood
      (taylorPairGraph G) (false,x) (false,y)) :
    2 * ((Finset.univ : Finset V).image
      (fun u => (Quotient.mk
        (closedTwinSetoid (taylorPairGraph G)) (false,u) :
        ClosedTwinQuotient (taylorPairGraph G)))).card ≤
      Fintype.card (ClosedTwinQuotient (taylorPairGraph G)) := by
  classical
  let H := taylorPairGraph G
  let Q := closedTwinQuotientGraph H
  let π : V → ClosedTwinQuotient H :=
    fun u => Quotient.mk (closedTwinSetoid H) (false,u)
  let I : Finset (ClosedTwinQuotient H) :=
    (Finset.univ : Finset V).image π
  obtain ⟨d,hd,hReg⟩ :=
    taylor_quotient_positive_regular G hTrans hEven
  have hInd :
      Q.IsIndepSet (Set.range π) :=
    eppa_selected_twin_classes_independent
      G H (EPPAIII.DoubleCover.bottomEmbedding V)
      heppa x y hXY hTwin
  have hSet : (I : Set (ClosedTwinQuotient H)) =
      Set.range π := by
    ext q
    simp [I,π]
  have hIndependent : Q.IsIndepSet
      (I : Set (ClosedTwinQuotient H)) := by
    simpa only [hSet] using hInd
  exact regular_graph_independent_card_le_half
    Q d hd hReg I hIndependent

end EPPAIII.TwoGraphs
