import EPPAIII.CliqueCovers.RegularHalfEdges
import EPPAIII.EPPA.Definitions

/-!
# Vertex-transitivity gives equal edge counts in two equal halves

This formalizes the remaining transitivity-to-regularity bridge for the
equal-half edge-count argument. An automorphism sends a vertex's
neighbour set bijectively onto the neighbour set of its image, hence
preserves its degree. If the action is vertex-transitive, the graph
has a common degree. We can therefore apply the independently
verified regular-host two-half counting argument.

The action is expressed explicitly through the EPPA-III definition
IsGraphAutomorphism, not a new external group-action axiom.
No EPPA, partition into outside cliques, or non-homogeneity is needed.
-/

namespace EPPAIII.CliqueCovers

/-- Actual vertex-transitivity under graph automorphisms of H. -/
def HasTransitiveGraphAutomorphisms {W : Type*}
    (H : SimpleGraph W) : Prop :=
  ∀ u v : W, ∃ q : Equiv.Perm W,
    EPPAIII.IsGraphAutomorphism H q ∧ q u = v

/-- Graph automorphisms preserve finite vertex degrees. -/
theorem graphAuto_preserves_degree
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (q : Equiv.Perm W) (hq : EPPAIII.IsGraphAutomorphism H q)
    (u : W) :
    H.degree (q u) = H.degree u := by
  classical
  have hMap :
      (H.neighborFinset u).map q.toEmbedding =
        H.neighborFinset (q u) := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,hvw⟩ := Finset.mem_map.mp hw
      have hvAdj : H.Adj u v :=
        (H.mem_neighborFinset u v).mp hv
      have hqAdj : H.Adj (q u) (q v) := (hq u v).mp hvAdj
      apply (H.mem_neighborFinset (q u) w).mpr
      rw [← hvw]
      exact hqAdj
    · intro hw
      refine Finset.mem_map.mpr ⟨q.symm w, ?_, by simp⟩
      apply (H.mem_neighborFinset u (q.symm w)).mpr
      apply (hq u (q.symm w)).mpr
      simpa using (H.mem_neighborFinset (q u) w).mp hw
  calc
    H.degree (q u) = (H.neighborFinset (q u)).card := rfl
    _ = ((H.neighborFinset u).map q.toEmbedding).card := by rw [hMap]
    _ = (H.neighborFinset u).card := Finset.card_map _
    _ = H.degree u := rfl

/-- Any finite nonempty vertex-transitive graph is regular. -/
theorem regular_of_transitive_graph
    {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hT : HasTransitiveGraphAutomorphisms H) :
    ∃ d : ℕ, H.IsRegularOfDegree d := by
  classical
  let origin : W := Classical.choice inferInstance
  refine ⟨H.degree origin, ?_⟩
  intro v
  obtain ⟨q,hq,hmap⟩ := hT origin v
  rw [← hmap]
  exact graphAuto_preserves_degree H q hq origin

/-- The two equal labelled halves of a vertex-transitive graph
have identical induced edge counts. -/
theorem sideEdges_equal_of_transitive_graph
    {V : Type*} [Fintype V] [Nonempty V]
    (H : SimpleGraph (Bool × V)) [DecidableRel H.Adj]
    (hT : HasTransitiveGraphAutomorphisms H) :
    sideEdgeCount H false =
      sideEdgeCount H true := by
  obtain ⟨d,hReg⟩ := regular_of_transitive_graph H hT
  exact sideEdges_equal_of_regular_graph H d hReg

end EPPAIII.CliqueCovers
