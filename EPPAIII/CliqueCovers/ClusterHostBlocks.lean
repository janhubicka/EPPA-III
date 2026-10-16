import EPPAIII.BlockSystems.ClusterObstructions
import EPPAIII.CliqueCovers.Basic

/-!
# Cross-block edges in cluster graph hosts

Assume both distinguished halves are unions of cliques, and the whole
host is also a disjoint union of cliques. No EPPA, external graph
classification, or vertex-transitivity hypothesis is used here.

Every nonempty cross-block adjacency is complete. Moreover the
incidence relation between the two collections of cliques is a partial
matching. Vertex-transitivity will be used later to show that this
partial matching is empty or perfect.
-/

namespace EPPAIII.CliqueCovers

/-- There is at least one edge between a selected clique and an
outside clique. -/
def HasCrossBlockEdge {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (i j : Fin s) : Prop :=
  ∃ a b : Fin t, H.Adj (left i a) (right j b)

private theorem left_ne_right {s t : ℕ}
    (i j : Fin s) (a b : Fin t) :
    left i a ≠ right j b := by
  intro h
  exact Bool.false_ne_true (congrArg Prod.fst h)

private theorem right_ne_left {s t : ℕ}
    (i j : Fin s) (a b : Fin t) :
    right i a ≠ left j b := by
  intro h
  exact Bool.true_ne_false (congrArg Prod.fst h)

/-- Cluster transitivity propagates any one edge between two clique
fibres to all pairs of their vertices. -/
theorem cluster_cross_block_complete {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H)
    (hLeft : ∀ i : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (left i a) (left i b))
    (hRight : ∀ j : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (right j a) (right j b))
    (i j : Fin s) (hCross : HasCrossBlockEdge H i j)
    (a b : Fin t) :
    H.Adj (left i a) (right j b) := by
  obtain ⟨a₀,b₀,hEdge⟩ := hCross
  have ha : H.Adj (left i a) (right j b₀) := by
    by_cases hSame : a = a₀
    · simpa [hSame] using hEdge
    · exact hCluster (left i a) (left i a₀) (right j b₀)
        (hLeft i a a₀ hSame) hEdge (left_ne_right i j a b₀)
  by_cases hSame : b = b₀
  · simpa [hSame] using ha
  · exact hCluster (left i a) (right j b₀) (right j b)
      ha (hRight j b₀ b (Ne.symm hSame)) (left_ne_right i j a b)

/-- Two different outside cliques cannot both connect to the same
selected clique inside a cluster host. -/
theorem cluster_cross_block_row_unique {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H)
    (hLeft : ∀ i : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (left i a) (left i b))
    (hRight : ∀ j : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (right j a) (right j b))
    (hRightSeparated : ∀ j k : Fin s, ∀ a b : Fin t,
      j ≠ k → ¬ H.Adj (right j a) (right k b))
    (i j k : Fin s)
    (hIJ : HasCrossBlockEdge H i j)
    (hIK : HasCrossBlockEdge H i k) : j = k := by
  by_contra hjk
  obtain ⟨a,b,_⟩ := hIJ
  obtain ⟨_,c,_⟩ := hIK
  have hab := cluster_cross_block_complete H hCluster hLeft hRight
    i j hIJ a b
  have hac := cluster_cross_block_complete H hCluster hLeft hRight
    i k hIK a c
  have hDifferent : right j b ≠ right k c := by
    intro hEq
    apply hjk
    exact congrArg (fun x : CoverVertex s t => x.2.1) hEq
  have hBC := hCluster (right j b) (left i a) (right k c)
    hab.symm hac hDifferent
  exact hRightSeparated j k b c hjk hBC

/-- Dually a fixed outside clique can meet at most one selected
clique. Thus nonempty cross blocks form a partial matching. -/
theorem cluster_cross_block_col_unique {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H)
    (hLeft : ∀ i : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (left i a) (left i b))
    (hRight : ∀ j : Fin s, ∀ a b : Fin t, a ≠ b →
      H.Adj (right j a) (right j b))
    (hLeftSeparated : ∀ i k : Fin s, ∀ a b : Fin t,
      i ≠ k → ¬ H.Adj (left i a) (left k b))
    (i k j : Fin s)
    (hIJ : HasCrossBlockEdge H i j)
    (hKJ : HasCrossBlockEdge H k j) : i = k := by
  by_contra hik
  obtain ⟨a,b,_⟩ := hIJ
  obtain ⟨c,_,_⟩ := hKJ
  have hab := cluster_cross_block_complete H hCluster hLeft hRight
    i j hIJ a b
  have hcb := cluster_cross_block_complete H hCluster hLeft hRight
    k j hKJ c b
  have hDifferent : left i a ≠ left k c := by
    intro hEq
    apply hik
    exact congrArg (fun x : CoverVertex s t => x.2.1) hEq
  have hAC := hCluster (left i a) (right j b) (left k c)
    hab hcb.symm hDifferent
  exact hLeftSeparated i k a c hik hAC

end EPPAIII.CliqueCovers
