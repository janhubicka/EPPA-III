import EPPAIII.BlockSystems.SmallHostPrimitivity
import EPPAIII.BlockSystems.SmallHostPairOrbits

/-!
# Primitive double-sized EPPA hosts are rank three

This module completes the nondegenerate equality case of the
small-host rank-three reduction in canonical balanced coordinates.

Every unordered host-pair orbit meets the designated bottom half:
if not, its orbital graph is a nonempty Aut(H)-invariant graph with
no internal bottom edges. Vertex transitivity forces equal numbers
of edges in the two halves, so it has no internal top edges either.
The preceding primitive-action obstruction then gives a contradiction.

After an orbit meets the bottom half, its original orientation can
be retained by choosing the correct ordering of the two base indices.
The fixed-embedding EPPA two-point orbit lemma then merges all
edge orbits and all nonedge orbits.

The strict-inequality branch (Neumann separation) and transport
to arbitrary host vertex coordinates remain separate obligations.
-/

namespace EPPAIII.BlockSystems

/-- Every unordered orbital graph of a primitive transitive host
with at least two vertices on each balanced side contains a pair
of vertices in the distinguished bottom half. -/
theorem primitive_balanced_unordered_orbit_hits_bottom
    {V : Type*} [Fintype V] [Nonempty V]
    (H : SimpleGraph (Bool × V))
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H)
    (x₀ y₀ : V) (hxy : x₀ ≠ y₀)
    (a b : Bool × V) (hab : a ≠ b) :
    ∃ x y : V,
      (unorderedPairOrbitGraph H a b hab).Adj
        (false,x) (false,y) := by
  classical
  let F : SimpleGraph (Bool × V) :=
    unorderedPairOrbitGraph H a b hab
  have hInv :
      ∀ (q : Equiv.Perm (Bool × V)),
        IsGraphAutomorphism H q → IsGraphAutomorphism F q := by
    intro q hq
    exact unorderedPairOrbitGraph_automorphism H a b hab q hq
  have hTransF :
      EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms F :=
    unorderedPairOrbitGraph_vertex_transitive H a b hab hTrans
  by_contra hNoOrbit
  have hNoBottom :
      ∀ x y : V, ¬ F.Adj (false,x) (false,y) := by
    intro x y h
    exact hNoOrbit ⟨x,y,h⟩
  have hNoTop :
      ∀ x y : V, ¬ F.Adj (true,x) (true,y) :=
    transitive_balanced_independent_half F hTransF hNoBottom
  have hCross :
      ∀ u v : Bool × V, F.Adj u v → u.1 ≠ v.1 := by
    rintro ⟨su,x⟩ ⟨sv,y⟩ huv heq
    cases su <;> cases sv
    · exact hNoBottom x y huv
    · cases heq
    · cases heq
    · exact hNoTop x y huv
  exact primitive_forbids_nonempty_invariant_cross_graph
    H F hPrim hInv hCross x₀ y₀ hxy a b
    (unorderedPairOrbitGraph_base_edge H a b hab)

/-- Under a primitive balanced action and at least two base
vertices, every ordered pair can be moved into the designated
bottom half. No EPPA assumption is needed for this coverage. -/
theorem primitive_balanced_selected_pair_coverage
    {V : Type*} [Fintype V] [Nonempty V]
    (H : SimpleGraph (Bool × V))
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H)
    (x₀ y₀ : V) (hxy₀ : x₀ ≠ y₀) :
    HasSelectedPairCoverage H
      (EPPAIII.DoubleCover.bottomEmbedding V) := by
  intro u v huv
  obtain ⟨x,y,hEdge⟩ :=
    primitive_balanced_unordered_orbit_hits_bottom
      H hTrans hPrim x₀ y₀ hxy₀ u v huv
  have hxy : x ≠ y := by
    intro heq
    exact ((unorderedPairOrbitGraph H u v huv).ne_of_adj hEdge)
      (by simpa [heq])
  rcases hEdge with ⟨q,hq,hPair⟩
  rcases hPair with ⟨hqu,hqv⟩ | ⟨hqu,hqv⟩
  · exact ⟨x,y,q,hxy,hq,hqu,hqv⟩
  · exact ⟨y,x,q,hxy.symm,hq,hqu,hqv⟩

/-- The nondegenerate |H|=2|G| primitive case of the rank-three
proposition, fully stated with the actual fixed EPPA embedding.
There is one orbit on ordered edges and one on ordered nonedges.
The complete and edgeless cases are included automatically. -/
theorem primitive_balanced_eppa_has_pair_orbits
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H)
    (x₀ y₀ : V) (hxy₀ : x₀ ≠ y₀) :
    HasOrderedPairOrbitByStatus H := by
  apply eppa_pair_status_orbits_of_selected_coverage
    G H (EPPAIII.DoubleCover.bottomEmbedding V) heppa
  exact primitive_balanced_selected_pair_coverage
    H hTrans hPrim x₀ y₀ hxy₀

/-- When each Boolean side has at most one vertex, a transitive
host has a single orbit on ordered distinct pairs. This includes
the empty-vertex case, where the statement is vacuous. -/
theorem transitive_subsingleton_double_has_pair_orbits
    {V : Type*} [Subsingleton V]
    (H : SimpleGraph (Bool × V))
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    HasOrderedPairOrbitByStatus H := by
  intro u v u' v' huv huv' _
  obtain ⟨q,hq,hqu⟩ := hTrans u u'
  have sideNe (w z : Bool × V) (hwz : w ≠ z) : w.1 ≠ z.1 := by
    intro h
    exact hwz (Prod.ext h (Subsingleton.elim w.2 z.2))
  have hqDiff : q u ≠ q v := q.injective.ne huv
  have hLeft : u'.1 ≠ (q v).1 := by
    have hh := sideNe (q u) (q v) hqDiff
    simpa [hqu] using hh
  have hRight : u'.1 ≠ v'.1 := sideNe u' v' huv'
  have hMatch : (q v).1 = v'.1 := by
    cases hU : u'.1 <;> cases hQ : (q v).1 <;>
      cases hV : v'.1 <;> simp_all
  exact ⟨q,hq,hqu,
    Prod.ext hMatch (Subsingleton.elim _ _)⟩

/-- Full primitive equality case, including the zero- and
one-vertex base graphs. No nontriviality assumption on V is needed. -/
theorem primitive_balanced_eppa_has_pair_orbits_all
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H
      (EPPAIII.DoubleCover.bottomEmbedding V))
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrim : IsPrimitiveAutAction H) :
    HasOrderedPairOrbitByStatus H := by
  classical
  by_cases hSub : Subsingleton V
  · letI : Subsingleton V := hSub
    exact transitive_subsingleton_double_has_pair_orbits H hTrans
  · have hDiff : ∃ x y : V, x ≠ y := by
      by_contra hNo
      apply hSub
      refine ⟨?_⟩
      intro x y
      by_contra hxy
      exact hNo ⟨x,y,hxy⟩
    obtain ⟨x,y,hxy⟩ := hDiff
    letI : Nonempty V := ⟨x⟩
    exact primitive_balanced_eppa_has_pair_orbits
      G H heppa hTrans hPrim x y hxy

end EPPAIII.BlockSystems
