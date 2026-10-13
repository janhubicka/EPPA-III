import EPPAIII.CliqueCovers.WagnerOutsideAction
import EPPAIII.CliqueCovers.WagnerSquareAction
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.CliqueCovers.CliqueUnionDegrees

/-!
# The outside half of the two-partial exceptional EPPA witness

The two partial coordinates force s=t=2. The four outside vertices
are labelled by the two selected points of their neighbourhood
profiles. EPPA lifts of the two independent within-clique swaps and
of the clique-index swap act as the three square symmetries on these
labels.

Consequently the outside induced graph is invariant under the
square dihedral action. Vertex-transitivity equates its edge count
with the designated 2K₂ (two edges), and the separately verified
finite square graph theorem forces the opposite-corner matching.

This is the full outside-graph step of the Wagner exception. The
last step of identifying the *entire eight-vertex host* with the
displayed Wagner graph and reducing to the short manuscript
replacement is independent and remains to be formalized.
-/

namespace EPPAIII.CliqueCovers

/-- The designated 2K₂ has exactly two edges. -/
theorem cliqueUnion_two_two_edge_count :
    (cliqueUnion 2 2).edgeSet.ncard = 2 := by
  classical
  have hReg : (cliqueUnion 2 2).IsRegularOfDegree 1 :=
    cliqueUnion_regular (by decide)
  have hSum :
      (∑ v : Fin 2 × Fin 2, (cliqueUnion 2 2).degree v) = 4 := by
    calc
      _ = ∑ _v : Fin 2 × Fin 2, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro v _
        exact hReg v
      _ = 4 := by decide
  have hDouble := (cliqueUnion 2 2).sum_degrees_eq_twice_card_edges
  have hEdges : (cliqueUnion 2 2).edgeFinset.card = 2 := by omega
  simpa only [← SimpleGraph.card_edgeSet,
    Set.fintypeCard_eq_ncard] using hEdges

/-- If the host is vertex-transitive and its double-partial
profile orbit saturates the complementary half, the outside
graph is precisely the opposite-corner matching. -/
theorem eppa_wagner_outside_is_opposite_matching
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    (outsideInducedGraph H e).comap
      (saturatedWagnerOutsideEquiv H e heppa hOrder w hw hBoth) =
        squareCornerGraph false true := by
  classical
  let label := saturatedWagnerOutsideEquiv
    H e heppa hOrder w hw hBoth
  let B := (outsideInducedGraph H e).comap label
  obtain ⟨QA,hQA,hACompat⟩ :=
    eppa_wagner_outside_flipFirst
      H e heppa hOrder w hw hBoth
  obtain ⟨QB,hQB,hBCompat⟩ :=
    eppa_wagner_outside_flipSecond
      H e heppa hOrder w hw hBoth
  obtain ⟨QC,hQC,hCCompat⟩ :=
    eppa_wagner_outside_swapCoordinates
      H e heppa hOrder w hw hBoth
  have hA : IsGraphAutomorphism B squareFlipFirst := by
    intro x y
    change H.Adj (label x).val (label y).val ↔
      H.Adj (label (squareFlipFirst x)).val
        (label (squareFlipFirst y)).val
    rw [← hACompat x, ← hACompat y]
    exact hQA (label x) (label y)
  have hB : IsGraphAutomorphism B squareFlipSecond := by
    intro x y
    change H.Adj (label x).val (label y).val ↔
      H.Adj (label (squareFlipSecond x)).val
        (label (squareFlipSecond y)).val
    rw [← hBCompat x, ← hBCompat y]
    exact hQB (label x) (label y)
  have hC : IsGraphAutomorphism B squareSwapCoordinates := by
    intro x y
    change H.Adj (label x).val (label y).val ↔
      H.Adj (label (squareSwapCoordinates x)).val
        (label (squareSwapCoordinates y)).val
    rw [← hCCompat x, ← hCCompat y]
    exact hQC (label x) (label y)
  let phi : (Fin 2 × Fin 2) ≃ Bool × Bool :=
    Equiv.prodCongr finTwoEquiv finTwoEquiv
  let labelFin : (Fin 2 × Fin 2) ≃ {u : W // u ∈ finiteOutside e} :=
    phi.trans label
  have hIntrinsic :
      ((outsideInducedGraph H e).comap labelFin).edgeSet.ncard =
        (cliqueUnion 2 2).edgeSet.ncard :=
    arbitrary_host_outside_edge_count_eq_base
      (cliqueUnion 2 2) H e heppa.1 labelFin hTransitive
  let iso :
      ((outsideInducedGraph H e).comap labelFin) ≃g B :=
    { toEquiv := phi
      map_rel_iff' := by
        intro x y
        rfl }
  have hReindex :
      ((outsideInducedGraph H e).comap labelFin).edgeFinset.card =
        B.edgeFinset.card :=
    iso.card_edgeFinset_eq
  have hFinEdges :
      ((outsideInducedGraph H e).comap labelFin).edgeFinset.card = 2 := by
    have hIntrinsicTwo := hIntrinsic.trans cliqueUnion_two_two_edge_count
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hIntrinsicTwo
  have hEdges : B.edgeFinset.card = 2 := hReindex.symm.trans hFinEdges
  exact square_invariant_two_edges_is_opposite_matching
    B hA hB hC hEdges

end EPPAIII.CliqueCovers
