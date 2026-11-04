import EPPAIII.EPPA.Definitions

/-!
# Transport of induced five-cycle obstructions through induced embeddings

This module isolates the functorial step required in Section 8 of EPPA III.
If G has an induced five-cycle and G embeds as an induced subgraph of H,
then H has an induced five-cycle. Equivalently, every induced subgraph
of a C5-free graph is C5-free.

There is no finiteness, polar geometry, group-action or classification
hypothesis. The proof uses only the *bidirectional* adjacency preservation
in the existing IsInducedGraphEmbedding interface.

The five nonedge pairs are explicitly required to consist of distinct
vertices. The ten pairwise inequalities also appear explicitly, so the
definition does not silently treat a closed walk as an induced cycle.
-/

namespace EPPAIII

/-- Exact ten-pair definition of a five-vertex induced cycle in a graph. -/
def IsInducedFiveCycleAt {V : Type*} (G : SimpleGraph V)
    (a b c d e : V) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧
   b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
   c ≠ d ∧ c ≠ e ∧ d ≠ e) ∧
  (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧
   G.Adj d e ∧ G.Adj e a) ∧
  (¬ G.Adj a c ∧ ¬ G.Adj a d ∧
   ¬ G.Adj b d ∧ ¬ G.Adj b e ∧ ¬ G.Adj c e)

/-- The global obstruction predicate. -/
def HasInducedFiveCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c d e : V, IsInducedFiveCycleAt G a b c d e

/-- Induced graph embeddings preserve induced five-cycles. -/
theorem induced_five_cycle_map
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (a b c d f : V)
    (h : IsInducedFiveCycleAt G a b c d f) :
    IsInducedFiveCycleAt H (e a) (e b) (e c) (e d) (e f) := by
  rcases h with ⟨hDist,hEdges,hNonedges⟩
  rcases hDist with
    ⟨hab,hac,had,haf,hbc,hbd,hbf,hcd,hcf,hdf⟩
  rcases hEdges with ⟨hAB,hBC,hCD,hDF,hFA⟩
  rcases hNonedges with ⟨hAC,hAD,hBD,hBF,hCF⟩
  refine ⟨?_,?_,?_⟩
  · exact ⟨e.injective.ne hab,e.injective.ne hac,
      e.injective.ne had,e.injective.ne haf,
      e.injective.ne hbc,e.injective.ne hbd,
      e.injective.ne hbf,e.injective.ne hcd,
      e.injective.ne hcf,e.injective.ne hdf⟩
  · exact ⟨(he a b).mp hAB,(he b c).mp hBC,
      (he c d).mp hCD,(he d f).mp hDF,(he f a).mp hFA⟩
  · exact ⟨
      (fun hh => hAC ((he a c).mpr hh)),
      (fun hh => hAD ((he a d).mpr hh)),
      (fun hh => hBD ((he b d).mpr hh)),
      (fun hh => hBF ((he b f).mpr hh)),
      (fun hh => hCF ((he c f).mpr hh))⟩

/-- An induced C5 in G also occurs in any induced-embedding host H. -/
theorem has_induced_five_cycle_of_embedding
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (h : HasInducedFiveCycle G) :
    HasInducedFiveCycle H := by
  rcases h with ⟨a,b,c,d,f,hCycle⟩
  exact ⟨e a,e b,e c,e d,e f,
    induced_five_cycle_map G H e he a b c d f hCycle⟩

/-- A graph with no induced C5 cannot contain an induced
embedding of any graph that does contain one. -/
theorem no_induced_five_cycle_of_embedding
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (hNo : ¬ HasInducedFiveCycle H) :
    ¬ HasInducedFiveCycle G := by
  intro h
  exact hNo (has_induced_five_cycle_of_embedding G H e he h)

end EPPAIII
