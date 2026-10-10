import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Every invariant-pair EPPA witness has uniform inter-fibre matrices

The previous module gives the pair-to-pair orbit transfer under the actual
EPPA condition. Here, assuming that the finite base graph has at least one
edge and at least one nonedge, we choose four Boolean parameters from two
reference pairs and prove that *every* inter-fibre adjacency is determined
by those parameters and the edge/nonedge type of its base pair.

This is the precise form of the two-point matrix reduction used in the
alternative proof of Claims 3.5--3.6 of EPPA-III.
-/

namespace EPPAIII.DoubleCover

/-- A uniform 2×2 fibre-matrix presentation. All parameters are actual
Boolean values, not postulated graph-theoretic properties. -/
def RepresentsPairPattern {V : Type*} (G : SimpleGraph V)
    (H : SimpleGraph (Bool × V)) (p : PairPattern) : Prop :=
  ∀ x y : V, x ≠ y →
    (H.Adj (false,x) (true,y) ↔
      (if G.Adj x y then p.crossEdge else p.crossNonedge) = true) ∧
    (H.Adj (true,x) (false,y) ↔
      (if G.Adj x y then p.crossEdge else p.crossNonedge) = true) ∧
    (H.Adj (true,x) (true,y) ↔
      (if G.Adj x y then p.topEdge else p.topNonedge) = true)

/-- A nontrivial finite base (containing an edge and a nonedge) admits
a canonical four-parameter description of all cross-fibre adjacencies.
No automorphism orbit of the complementary half is assumed. -/
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
  refine ⟨⟨ce,cn,te,tn⟩, ?_⟩
  intro x y hxy
  by_cases hadj : G.Adj x y
  · have hrel : G.Adj x y ↔ G.Adj xe ye :=
      ⟨fun _ => hEdge, fun _ => hadj⟩
    have hu := eppa_uniform_pair_entries G H heppa hPairs
      x y xe ye hxy (G.ne_of_adj hEdge) hrel
    have hs := eppa_cross_symmetric G H heppa hPairs x y hxy
    refine ⟨?_, ?_, ?_⟩
    · simpa [hadj, ce] using hu.1
    · exact hs.symm.trans (by simpa [hadj, ce] using hu.1)
    · simpa [hadj, te] using hu.2.2
  · have hrel : G.Adj x y ↔ G.Adj xn yn :=
      ⟨fun h => False.elim (hadj h),
       fun h => False.elim (hNonedge h)⟩
    have hu := eppa_uniform_pair_entries G H heppa hPairs
      x y xn yn hxy hNonDistinct hrel
    have hs := eppa_cross_symmetric G H heppa hPairs x y hxy
    refine ⟨?_, ?_, ?_⟩
    · simpa [hadj, cn] using hu.1
    · exact hs.symm.trans (by simpa [hadj, cn] using hu.1)
    · simpa [hadj, tn] using hu.2.2

/-- The two diagonal entries of the inter-fibre matrix are exactly
the base graph relation and the top-layer parameter, respectively. -/
theorem induced_pair_bottom {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (x y : V) :
    H.Adj (false,x) (false,y) ↔ G.Adj x y :=
  (heppa.1 x y).symm

end EPPAIII.DoubleCover
