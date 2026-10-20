import EPPAIII.TwoGraphs.TaylorSelectedTwinHomogeneity
import EPPAIII.TwoGraphs.TwinTransversalCardinality
import EPPAIII.TwoGraphs.TaylorEppaTransitivity
import EPPAIII.TwoGraphs.TaylorBadPairTwins

/-!
# Full even-triple pair coverage in an EPPA Taylor double

This assembles the two already-verified cases of the true-twin quotient
argument in Section 5 fibre rigidity.

If a base pair lies in no even triple, an adjacent pair of their
Taylor lifts consists of true twins. EPPA plus the deck involution
makes the host vertex-transitive. If some selected edge is internal
to a true-twin class, the occupied-class counting theorem forces
the selected graph to be homogeneous. Otherwise selected vertices
are in pairwise distinct twin classes; the double-size quotient
argument again forces homogeneity.

Thus a non-homogeneous base with at least one even triple has no
bad pair. No classification of homogeneous graphs is used.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- A missing even-parity triple through a distinct base pair
contradicts EPPA and non-homogeneity in a nontrivial two-graph. -/
theorem taylor_eppa_bad_pair_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G (taylorPairGraph G)
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (hEven : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      EvenTriple G a b c)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph G)
    (x y : V) (hxy : x ≠ y)
    (hBad : ∀ z : V, x ≠ z → y ≠ z →
      ¬ EvenTriple G x y z) : False := by
  classical
  let H : SimpleGraph (Bool × V) := taylorPairGraph G
  have hTrans : HasTransitiveGraphAutomorphisms H :=
    taylor_double_vertex_transitive_of_eppa G heppa
  let c : Bool := if G.Adj x y then false else true
  have hAdj : H.Adj (false,x) (c,y) := by
    change x ≠ y ∧ (G.Adj x y ↔ false = c)
    refine ⟨hxy,?_⟩
    dsimp [c]
    by_cases h : G.Adj x y <;> simp [h]
  have hTwin : SameClosedNeighbourhood H (false,x) (c,y) :=
    taylor_bad_pair_adjacent_true_twins G x y false c hAdj hBad
  have hDistinct : (false,x) ≠ (c,y) := by
    intro h
    exact hxy (congrArg Prod.snd h)
  have hSelfMem : (false,x) ∈ closedTwinClass H (false,x) := by
    simp [closedTwinClass,SameClosedNeighbourhood]
  have hTwinMem : (c,y) ∈ closedTwinClass H (false,x) := by
    simp only [closedTwinClass,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hTwin
  have hSubset :
      ({(false,x),(c,y)} : Finset (Bool × V)) ⊆
        closedTwinClass H (false,x) := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hSelfMem
    · exact hTwinMem
  have hLarge : 2 ≤ (closedTwinClass H (false,x)).card := by
    have hTwo : ({(false,x),(c,y)} : Finset (Bool × V)).card = 2 := by
      simp [hDistinct,hDistinct.symm]
    calc
      2 = ({(false,x),(c,y)} : Finset (Bool × V)).card :=
        hTwo.symm
      _ ≤ (closedTwinClass H (false,x)).card :=
        Finset.card_le_card hSubset
  by_cases hSelectedTwinEdge :
      ∃ u v : V, G.Adj u v ∧
        SameClosedNeighbourhood H (false,u) (false,v)
  · obtain ⟨u,v,hEdge,hUTwin⟩ := hSelectedTwinEdge
    exact hNonhomogeneous
      (taylor_eppa_selected_true_twin_edge_homogeneous
        G heppa hTrans hEven u v hEdge hUTwin)
  · have hSeparated : ∀ u v : V,
        SameClosedNeighbourhood H (false,u) (false,v) →
          u = v := by
      intro u v hUV
      by_contra huv
      have hUVDistinct : (false,u) ≠ (false,v) := by
        intro hh
        exact huv (congrArg Prod.snd hh)
      have hHostEdge : H.Adj (false,u) (false,v) :=
        adjacent_of_same_closed_neighbourhood
          H (false,u) (false,v) hUVDistinct hUV
      have hBaseEdge : G.Adj u v :=
        (heppa.1 u v).mpr hHostEdge
      exact hSelectedTwinEdge ⟨u,v,hBaseEdge,hUV⟩
    have hDouble :
        Fintype.card (Bool × V) = 2 * Fintype.card V := by
      simp [Fintype.card_prod]
    exact hNonhomogeneous
      (double_eppa_separated_twin_classes_homogeneous
        G H (EPPAIII.DoubleCover.bottomEmbedding V)
        heppa hDouble hTrans x hLarge hSeparated)

/-- Every distinct base pair lies in an even-parity triple, under
the actual EPPA and non-homogeneous hypotheses and with at least
one even triple somewhere in the two-graph. -/
theorem taylor_eppa_even_triple_pair_coverage
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (closedTwinQuotientGraph (taylorPairGraph G)).Adj]
    (heppa : IsEPPAEmbedding G (taylorPairGraph G)
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (hEven : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      EvenTriple G a b c)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph G) :
    ∀ x y : V, x ≠ y →
      ∃ z : V, x ≠ z ∧ y ≠ z ∧ EvenTriple G x y z := by
  classical
  intro x y hxy
  by_contra hNo
  have hBad : ∀ z : V, x ≠ z → y ≠ z →
      ¬ EvenTriple G x y z := by
    intro z hxz hyz hEven'
    exact hNo ⟨z,hxz,hyz,hEven'⟩
  exact taylor_eppa_bad_pair_impossible
    G heppa hEven hNonhomogeneous x y hxy hBad

end EPPAIII.TwoGraphs
