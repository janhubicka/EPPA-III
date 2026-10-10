import EPPAIII.DoubleCover.FibreEdgeCount

/-!
# Excluding the two non-Taylor balanced fibre patterns

For a non-homogeneous finite graph G in an invariant-pair EPPA witness,
the numerical argument leaves exactly three patterns. The one-edge and
three-edge patterns each admit an invariant exceptional relation (the
unique inter-fibre edge or nonedge) which forces every automorphism
fixing one bottom vertex to fix the bottom layer setwise. The already
formalized LayerRigidity/Homogeneity argument then contradicts
non-homogeneity.

Consequently all inter-fibre edges are those of the Taylor double.
Only the uniform presence/absence of the mate edges remains free.
-/

namespace EPPAIII.DoubleCover

theorem oneEdge_forces_homogeneous {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hr : RepresentsPairPattern G H oneEdge) :
    IsHomogeneousGraph G := by
  have hOccurs : ∀ x y : V, x ≠ y → ∃ b : Bool,
      (if false then ¬ H.Adj (b,x) (b,y) else H.Adj (b,x) (b,y)) := by
    intro x y hxy
    by_cases hEdge : G.Adj x y
    · exact ⟨false, (heppa.1 x y).mp hEdge⟩
    · have hTop := (hr.2 x y hxy hEdge).2.2
      exact ⟨true, hTop.mpr (by decide)⟩
  have hSame : ∀ u v : Bool × V, u.2 ≠ v.2 →
      (if false then ¬ H.Adj u v else H.Adj u v) → u.1 = v.1 := by
    intro u v hDifferent hAdj
    rcases u with ⟨b,x⟩
    rcases v with ⟨c,y⟩
    change x ≠ y at hDifferent
    cases b <;> cases c
    · rfl
    · have hCross : ¬ H.Adj (false,x) (true,y) := by
        by_cases hEdge : G.Adj x y
        · simpa [oneEdge] using (hr.1 x y hDifferent hEdge).1
        · simpa [oneEdge] using (hr.2 x y hDifferent hEdge).1
      exact False.elim (hCross hAdj)
    · have hCross : ¬ H.Adj (true,x) (false,y) := by
        by_cases hEdge : G.Adj x y
        · simpa [oneEdge] using (hr.1 x y hDifferent hEdge).2.1
        · simpa [oneEdge] using (hr.2 x y hDifferent hEdge).2.1
      exact False.elim (hCross hAdj)
    · rfl
  exact homogeneous_of_graph_exceptional
    G H heppa hPairs false hOccurs hSame

theorem threeEdges_forces_homogeneous {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hr : RepresentsPairPattern G H threeEdges) :
    IsHomogeneousGraph G := by
  have hOccurs : ∀ x y : V, x ≠ y → ∃ b : Bool,
      (if true then ¬ H.Adj (b,x) (b,y) else H.Adj (b,x) (b,y)) := by
    intro x y hxy
    by_cases hEdge : G.Adj x y
    · have hTop := (hr.1 x y hxy hEdge).2.2
      refine ⟨true, ?_⟩
      simpa [threeEdges] using hTop
    · refine ⟨false, ?_⟩
      intro h
      exact hEdge ((heppa.1 x y).mpr h)
  have hSame : ∀ u v : Bool × V, u.2 ≠ v.2 →
      (if true then ¬ H.Adj u v else H.Adj u v) → u.1 = v.1 := by
    intro u v hDifferent hNotAdj
    rcases u with ⟨b,x⟩
    rcases v with ⟨c,y⟩
    change x ≠ y at hDifferent
    cases b <;> cases c
    · rfl
    · have hCross : H.Adj (false,x) (true,y) := by
        by_cases hEdge : G.Adj x y
        · simpa [threeEdges] using (hr.1 x y hDifferent hEdge).1
        · simpa [threeEdges] using (hr.2 x y hDifferent hEdge).1
      exact False.elim (hNotAdj hCross)
    · have hCross : H.Adj (true,x) (false,y) := by
        by_cases hEdge : G.Adj x y
        · simpa [threeEdges] using (hr.1 x y hDifferent hEdge).2.1
        · simpa [threeEdges] using (hr.2 x y hDifferent hEdge).2.1
      exact False.elim (hNotAdj hCross)
    · rfl
  exact homogeneous_of_graph_exceptional
    G H heppa hPairs true hOccurs hSame

/-- The graph-theoretic conclusion of the balanced-pattern analysis,
without treating the within-fibre mate edges as determined. -/
theorem nonhomogeneous_pair_pattern_is_taylor {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (p : PairPattern) (hr : RepresentsPairPattern G H p)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    p = taylor := by
  rcases nonhomogeneous_pair_pattern_cases
      G H heppa hPairs p hr hNonHomogeneous with h1 | h2 | h3
  · subst p
    exact False.elim (hNonHomogeneous
      (oneEdge_forces_homogeneous G H heppa hPairs hr))
  · exact h2
  · subst p
    exact False.elim (hNonHomogeneous
      (threeEdges_forces_homogeneous G H heppa hPairs hr))

/-- Under true EPPA, an invariant pair system, and non-homogeneity,
an edge and a nonedge of G suffice to identify every inter-fibre
edge of H with the corresponding Taylor double edge. -/
theorem eppa_taylor_interfibre {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (xe ye xn yn : V)
    (hEdge : G.Adj xe ye)
    (hNonDistinct : xn ≠ yn)
    (hNonedge : ¬ G.Adj xn yn) :
    RepresentsPairPattern G H taylor := by
  obtain ⟨p,hr⟩ := eppa_has_uniform_pair_pattern
    G H heppa hPairs xe ye xn yn hEdge hNonDistinct hNonedge
  have hp := nonhomogeneous_pair_pattern_is_taylor
    G H heppa hPairs p hr hNonHomogeneous
  simpa [hp] using hr

end EPPAIII.DoubleCover
