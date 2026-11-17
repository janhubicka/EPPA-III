import EPPAIII.TwoGraphs.FourWayAllOrders
import EPPAIII.BlockSystems.RookThreeBase

/-!
# Exact finite two-graph model list in the four-way theorem

The homogeneous two-graph classification in the manuscript asserts
that the only models are the empty and complete two-graphs, and unique
nontrivial models on 6 and 10 points.

The nontrivial *representatives* are defined here by isolating one
vertex and putting C5 or the 3x3 rook graph on the remaining vertices.
The external assertion that these are the only homogeneous finite
two-graphs is an EXPLICIT premise of the final four-way theorem.
No Lean axiom or circular classification proof is introduced.

The internal equivalences (some nonhomogeneous EPPA transversal,
all EPPA transversals, and homogeneous two-graph) are proved in
FourWayInternalEquivalence and FourWayAllOrders.
-/

namespace EPPAIII.TwoGraphs

/-- Six-point representative of the exceptional two-graph:
the five-cycle with one isolated vertex. -/
def cycleFiveWithIsolated : SimpleGraph (Option (Fin 5)) :=
  SimpleGraph.fromRel (fun a b =>
    match a,b with
    | some x,some y => (SimpleGraph.cycleGraph 5).Adj x y
    | _,_ => False)

/-- Ten-point representative of the exceptional two-graph:
the 3x3 rook graph with one isolated vertex. -/
def rookThreeWithIsolated :
    SimpleGraph (Option EPPAIII.BlockSystems.rookVertex) :=
  SimpleGraph.fromRel (fun a b =>
    match a,b with
    | some x,some y => EPPAIII.BlockSystems.rookThreeGraph.Adj x y
    | _,_ => False)

/-- The literal four cases in the Section 5 classification.
The last two clauses specify actual graph relabellings which
preserve odd-edge triple parity, not a mere cardinality condition. -/
noncomputable def ClassifiedHomogeneousTwoGraph
    {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : Prop := by
  classical
  exact
    (∀ x y z : V, ¬ OddBaseTriple G x y z) ∨
    (∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
      OddBaseTriple G x y z) ∨
    (∃ φ : Option (Fin 5) ≃ V,
      ∀ a b c : Option (Fin 5),
        OddBaseTriple cycleFiveWithIsolated a b c ↔
          OddBaseTriple G (φ a) (φ b) (φ c)) ∨
    (∃ φ : Option EPPAIII.BlockSystems.rookVertex ≃ V,
      ∀ a b c : Option EPPAIII.BlockSystems.rookVertex,
        OddBaseTriple rookThreeWithIsolated a b c ↔
          OddBaseTriple G (φ a) (φ b) (φ c))

/-- The literal four-way theorem, relative precisely to the
external finite homogeneous-two-graph classification expressed
by the preceding four canonical alternatives. -/
theorem fourway_exact_named_twograph_models_relative_to_classification
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hExternalClassification :
      IsHomogeneousTwoGraph G ↔ ClassifiedHomogeneousTwoGraph G)
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ((∃ t : V → Bool,
      ¬ DoubleCover.IsHomogeneousGraph (taylorTransversalGraph G t) ∧
      EPPAIII.IsEPPAEmbedding
        (taylorTransversalGraph G t) (taylorPairGraph G)
        (taylorTransversalEmbedding t)) ↔
     (∀ t : V → Bool,
       EPPAIII.IsEPPAEmbedding
         (taylorTransversalGraph G t) (taylorPairGraph G)
         (taylorTransversalEmbedding t))) ∧
    ((∀ t : V → Bool,
       EPPAIII.IsEPPAEmbedding
         (taylorTransversalGraph G t) (taylorPairGraph G)
         (taylorTransversalEmbedding t)) ↔
      IsHomogeneousTwoGraph G) ∧
    (IsHomogeneousTwoGraph G ↔ ClassifiedHomogeneousTwoGraph G) := by
  have hAllIffHom :=
    all_taylor_transversals_eppa_iff_homogeneous_two_graph G
  have hExistIffBoth :=
    taylor_fourway_internal_equivalence G x y z hxy hxz hyz
  constructor
  · constructor
    · intro hSome
      exact (hExistIffBoth.mp hSome).1
    · intro hAll
      exact hExistIffBoth.mpr ⟨hAll,hAllIffHom.mp hAll⟩
  exact ⟨hAllIffHom,hExternalClassification⟩

end EPPAIII.TwoGraphs
