import EPPAIII.DoubleCover.PairPatterns
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Uniform four-bit inter-fibre matrices derived from EPPA

For a finite base with an edge and a nonedge, exact EPPA and invariance of
the two-element fibres construct one Boolean matrix for all pairs over
base edges, and another for all pairs over base nonedges.

We deliberately state the edge and nonedge cases separately, so this
proposition does not require an arbitrary decidability choice for G.Adj.
-/

namespace EPPAIII.DoubleCover

/-- A uniform 2×2 fibre-matrix presentation with genuinely fixed
Boolean parameters, not an extra symmetry assumption. -/
def RepresentsPairPattern {V : Type*} (G : SimpleGraph V)
    (H : SimpleGraph (Bool × V)) (p : PairPattern) : Prop :=
  (∀ x y : V, x ≠ y → G.Adj x y →
    (H.Adj (false,x) (true,y) ↔ p.crossEdge = true) ∧
    (H.Adj (true,x) (false,y) ↔ p.crossEdge = true) ∧
    (H.Adj (true,x) (true,y) ↔ p.topEdge = true)) ∧
  (∀ x y : V, x ≠ y → ¬ G.Adj x y →
    (H.Adj (false,x) (true,y) ↔ p.crossNonedge = true) ∧
    (H.Adj (true,x) (false,y) ↔ p.crossNonedge = true) ∧
    (H.Adj (true,x) (true,y) ↔ p.topNonedge = true))

/-- Four actual Boolean values, chosen from one edge and one nonedge,
specify all inter-fibre adjacency matrices. -/
theorem eppa_has_uniform_pair_pattern {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (xe ye xn yn : V)
    (hEdge : G.Adj xe ye)
    (hNonDistinct : xn ≠ yn)
    (hNonedge : ¬ G.Adj xn yn) :
    ∃ p : PairPattern, RepresentsPairPattern G H p := by
  classical
  let ce : Bool := decide (H.Adj (false,xe) (true,ye))
  let cn : Bool := decide (H.Adj (false,xn) (true,yn))
  let te : Bool := decide (H.Adj (true,xe) (true,ye))
  let tn : Bool := decide (H.Adj (true,xn) (true,yn))
  refine ⟨⟨ce,cn,te,tn⟩, ?_, ?_⟩
  · intro x y hxy hadj
    have hrel : G.Adj x y ↔ G.Adj xe ye :=
      ⟨fun _ => hEdge, fun _ => hadj⟩
    have hu := eppa_uniform_pair_entries G H heppa hPairs
      x y xe ye hxy (G.ne_of_adj hEdge) hrel
    have hs := eppa_cross_symmetric G H heppa hPairs x y hxy
    refine ⟨?_, ?_, ?_⟩
    · simpa [ce] using hu.1
    · exact hs.symm.trans (by simpa [ce] using hu.1)
    · simpa [te] using hu.2.2
  · intro x y hxy hnot
    have hrel : G.Adj x y ↔ G.Adj xn yn :=
      ⟨fun h => False.elim (hnot h),
       fun h => False.elim (hNonedge h)⟩
    have hu := eppa_uniform_pair_entries G H heppa hPairs
      x y xn yn hxy hNonDistinct hrel
    have hs := eppa_cross_symmetric G H heppa hPairs x y hxy
    refine ⟨?_, ?_, ?_⟩
    · simpa [cn] using hu.1
    · exact hs.symm.trans (by simpa [cn] using hu.1)
    · simpa [tn] using hu.2.2

/-- The selected bottom-to-bottom entries are exactly those of G. -/
theorem induced_pair_bottom {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (x y : V) :
    H.Adj (false,x) (false,y) ↔ G.Adj x y :=
  (heppa.1 x y).symm

end EPPAIII.DoubleCover
