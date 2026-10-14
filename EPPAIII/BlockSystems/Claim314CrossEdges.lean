import EPPAIII.BlockSystems.OccupiedBlockAction
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.CliqueCovers.SpanningEdgeRigidity

/-!
# Claim 3.14: no cross-block edges in the outside half

Let J be the graph retaining only the edges of H between different
blocks of an Aut(H)-invariant partition. The actual automorphisms of
H preserve J and act transitively on it whenever H is vertex
transitive. If all edges of the distinguished induced copy G lie
inside individual blocks, the selected half is independent in J.

For |H|=2|G|, the already proved arbitrary-host equal-half
edge-count theorem applied to J says that the complementary half
also has no J-edges. Consequently *every* inter-block edge of H
joins a selected vertex to an outside vertex.

There is no need to deduce D-side block regularity or to assume
the complementary half forms a particular clique partition.
-/

namespace EPPAIII.BlockSystems

/-- Only inter-block edges of H; this graph records their actual
individual endpoints, not just an edge between block labels. -/
def crossBlockGraph {W B : Type*}
    (H : SimpleGraph W) (block : W → B) : SimpleGraph W where
  Adj := fun u v => H.Adj u v ∧ block u ≠ block v
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact H.irrefl h.1

/-- Every genuine host automorphism acts on the cross-block graph. -/
theorem crossBlockGraph_graphAut {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism (crossBlockGraph H block) q := by
  intro u v
  change (H.Adj u v ∧ block u ≠ block v) ↔
    (H.Adj (q u) (q v) ∧ block (q u) ≠ block (q v))
  constructor
  · rintro ⟨hAdj,hDiff⟩
    exact ⟨(hq u v).mp hAdj,
      fun hSame => hDiff ((hBlocks q hq u v).mpr hSame)⟩
  · rintro ⟨hAdj,hDiff⟩
    exact ⟨(hq u v).mpr hAdj,
      fun hSame => hDiff ((hBlocks q hq u v).mp hSame)⟩

/-- Host vertex-transitivity also gives vertex-transitivity
of the cross-block-edge graph, including when it is empty. -/
theorem crossBlockGraph_transitive {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    CliqueCovers.HasTransitiveGraphAutomorphisms
      (crossBlockGraph H block) := by
  intro u v
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  exact ⟨q,crossBlockGraph_graphAut H block hBlocks q hq,hqu⟩

/-- Any graph with no edges is the bottom graph; the statement
uses intrinsic finite edge-set cardinality. -/
theorem graph_eq_bot_of_edgeSet_ncard_zero {V : Type*}
    [Fintype V]
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (hZero : J.edgeSet.ncard = 0) :
    J = ⊥ := by
  classical
  have hEdges : J.edgeFinset.card = 0 := by
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hZero
  exact (CliqueCovers.graph_eq_of_le_of_edge_card_eq
    (⊥ : SimpleGraph V) J bot_le
    (by simp [hEdges])).symm

/-- The double-order assumption provides an actual equivalence
between selected and complementary vertex types, with no further
structure or EPPA property needed. -/
noncomputable def balancedOutsideEquivGeneral {V W : Type*}
    [Fintype V] [Fintype W]
    (e : V ↪ W)
    (hDouble : Fintype.card W = 2 * Fintype.card V) :
    V ≃ {u : W // u ∈ finiteOutside e} := by
  classical
  apply Fintype.equivOfCardEq
  calc
    Fintype.card V = Fintype.card W - Fintype.card V := by omega
    _ = (finiteOutside e).card := (finiteOutside_card e).symm
    _ = Fintype.card {u : W // u ∈ finiteOutside e} := by
      simp only [Fintype.card_coe]

/-- Because the selected copy has no cross-block edges,
the induced cross-block graph on the outside half is empty as well. -/
theorem crossBlockGraph_outside_bot {V W B : Type*}
    [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj]
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hDouble : Fintype.card W = 2 * Fintype.card V) :
    CliqueCovers.outsideInducedGraph (crossBlockGraph H block) e = ⊥ := by
  classical
  let J := crossBlockGraph H block
  let f := balancedOutsideEquivGeneral e hDouble
  have hJBase : IsInducedGraphEmbedding (⊥ : SimpleGraph V) J e := by
    intro x y
    change False ↔
      (H.Adj (e x) (e y) ∧ block (e x) ≠ block (e y))
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨hAdj,hDiff⟩
      exact False.elim (hDiff
        (hSelectedInside x y ((he x y).mpr hAdj)))
  have hJTrans : CliqueCovers.HasTransitiveGraphAutomorphisms J :=
    crossBlockGraph_transitive H block hBlocks hTrans
  have hEqEdges :
      ((CliqueCovers.outsideInducedGraph J e).comap f).edgeSet.ncard =
        (⊥ : SimpleGraph V).edgeSet.ncard :=
    CliqueCovers.arbitrary_host_outside_edge_count_eq_base
      (⊥ : SimpleGraph V) J e hJBase f hJTrans
  have hZero :
      ((CliqueCovers.outsideInducedGraph J e).comap f).edgeSet.ncard = 0 := by
    simpa using hEqEdges
  have hBot :
      (CliqueCovers.outsideInducedGraph J e).comap f = ⊥ :=
    graph_eq_bot_of_edgeSet_ncard_zero
      ((CliqueCovers.outsideInducedGraph J e).comap f) hZero
  apply SimpleGraph.ext
  funext u v
  apply propext
  constructor
  · intro hAdj
    have hAt : ((CliqueCovers.outsideInducedGraph J e).comap f).Adj
        (f.symm u) (f.symm v) := by
      simpa using hAdj
    rw [hBot] at hAt
    exact False.elim hAt
  · intro h
    exact False.elim h

/-- Claim 3.14: there are no inter-block edges joining two
vertices outside the designated induced copy. -/
theorem no_outside_cross_block_edges {V W B : Type*}
    [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel H.Adj]
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSelectedInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (u v : W) (hu : u ∉ Set.range e) (hv : v ∉ Set.range e)
    (hAdj : H.Adj u v) :
    block u = block v := by
  classical
  have hOutside :=
    crossBlockGraph_outside_bot
      G H e he block hBlocks hTrans hSelectedInside hDouble
  have huOutside : u ∈ finiteOutside e := by
    simpa [finiteOutside] using hu
  have hvOutside : v ∈ finiteOutside e := by
    simpa [finiteOutside] using hv
  have hNo :
      ¬ (crossBlockGraph H block).Adj u v := by
    have hh : ¬ (CliqueCovers.outsideInducedGraph
        (crossBlockGraph H block) e).Adj
        ⟨u,huOutside⟩ ⟨v,hvOutside⟩ := by
      rw [hOutside]
      simp
    exact hh
  by_contra hDifferent
  exact hNo ⟨hAdj,hDifferent⟩

end EPPAIII.BlockSystems
