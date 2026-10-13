import EPPAIII.CliqueCovers.MaskCoverDegree
import EPPAIII.CliqueCovers.ZeroPartialOutsideConclusion
import EPPAIII.CliqueCovers.OutsideMaskAction

/-!
# The actual zero-partial host is an all-or-nothing masked clique cover

Once the true-twin quotient labels the outside half by s fibres of
t vertices, every cross-block is either entirely full or entirely
empty. The adjacency matrix is consequently described by one
subset of the selected clique indices for every outside fibre.

This file proves that the actual host graph is equal to the
general masked model, under the labelling which preserves the base
embedding. Vertex-transitivity then yields *equal cardinalities of
all these masks* from the explicit degree formula of MaskCoverDegree.

Together with the genuine EPPA mask-orbit coverage and four-normal-
forms theorems, this will identify the final zero-partial host
with a uniform generalized clique cover.
-/

namespace EPPAIII.CliqueCovers

/-- The actual complete/empty mask of an outside true-twin fibre,
using a fixed anchor coordinate a in both halves. -/
noncomputable def zeroPartialOutsideMask {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e}) :
    Fin s → Finset (Fin s) :=
  fun j => outsideIndexMask H e a (label (j,a)).val

/-- Cross adjacency depends only on the two clique indices,
not on coordinates within either clique. The base-coordinate
independence follows from no-partial profiles and the outside-
coordinate independence follows from closed-twin fibre labels. -/
theorem zero_partial_cross_adj_iff_mask {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (hNoPartial : ∀ u : W, u ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = t)
    (anchor : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (i j : Fin s) (a b : Fin t) :
    H.Adj (label (j,b)).val (e (i,a)) ↔
      i ∈ zeroPartialOutsideMask H e anchor label j := by
  classical
  have hu : (label (j,b)).val ∉ Set.range e := by
    simpa [finiteOutside] using (label (j,b)).property
  have hv : (label (j,anchor)).val ∉ Set.range e := by
    simpa [finiteOutside] using (label (j,anchor)).property
  have hNeU : (label (j,b)).val ≠ e (i,a) := by
    intro hEq
    exact hu ⟨(i,a),hEq.symm⟩
  have hNeV : (label (j,anchor)).val ≠ e (i,a) := by
    intro hEq
    exact hv ⟨(i,a),hEq.symm⟩
  have hTwin :
      H.Adj (label (j,b)).val (e (i,a)) ↔
        H.Adj (label (j,anchor)).val (e (i,a)) :=
    adj_iff_of_same_closed_neighbourhood_left H
      _ _ _ (hFibre j b anchor) hNeU hNeV
  have hSelected :
      H.Adj (label (j,anchor)).val (e (i,a)) ↔
        H.Adj (label (j,anchor)).val (e (i,anchor)) :=
    outside_adj_uniform_of_no_partial H e hNoPartial
      _ hv i a anchor
  have hMask :
      H.Adj (label (j,anchor)).val (e (i,anchor)) ↔
        i ∈ zeroPartialOutsideMask H e anchor label j := by
    simp [zeroPartialOutsideMask, outsideIndexMask]
  exact hTwin.trans (hSelected.trans hMask)

/-- The host graph in the actual labelled two-half coordinates is
exactly the all-or-nothing mask graph, without any additional
symmetry assumption beyond the twin fibre and no-partial premises. -/
theorem zero_partial_host_eq_maskCoverGraph {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ u : W, u ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = t)
    (anchor : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (hOutside : (outsideInducedGraph H e).comap label = cliqueUnion s t) :
    H.comap (balancedHostEquiv e label) =
      maskCoverGraph s t (zeroPartialOutsideMask H e anchor label) := by
  classical
  let mask := zeroPartialOutsideMask H e anchor label
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy
  · change H.Adj (e (i,a)) (e (j,b)) ↔
      maskCoverAdj mask (false,(i,a)) (false,(j,b))
    simpa [maskCoverAdj,cliqueUnion] using (he (i,a) (j,b)).symm
  · change H.Adj (e (i,a)) (label (j,b)).val ↔
      maskCoverAdj mask (false,(i,a)) (true,(j,b))
    have hSym :
        H.Adj (e (i,a)) (label (j,b)).val ↔
          H.Adj (label (j,b)).val (e (i,a)) :=
      H.adj_comm _ _
    have hCross := zero_partial_cross_adj_iff_mask
      H e hNoPartial anchor label hFibre i j a b
    simpa [maskCoverAdj,mask] using hSym.trans hCross
  · change H.Adj (label (i,a)).val (e (j,b)) ↔
      maskCoverAdj mask (true,(i,a)) (false,(j,b))
    have hCross := zero_partial_cross_adj_iff_mask
      H e hNoPartial anchor label hFibre j i b a
    simpa [maskCoverAdj,mask] using hCross
  · change H.Adj (label (i,a)).val (label (j,b)).val ↔
      maskCoverAdj mask (true,(i,a)) (true,(j,b))
    have hRight :
        H.Adj (label (i,a)).val (label (j,b)).val ↔
          (cliqueUnion s t).Adj (i,a) (j,b) := by
      change ((outsideInducedGraph H e).comap label).Adj (i,a) (j,b) ↔
        (cliqueUnion s t).Adj (i,a) (j,b)
      rw [hOutside]
    simpa [maskCoverAdj,cliqueUnion] using hRight

/-- Vertex-transitivity of an actual zero-partial host implies
all outside true-twin clique-index masks have the same size.
This discharges the numerical regularity hypothesis needed by
the EPPA four-normal-form theorem. -/
theorem zero_partial_outside_masks_uniform_of_transitive {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ u : W, u ∉ Set.range e →
      ∀ i : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e u) i).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (anchor : Fin t)
    (label : (Fin s × Fin t) ≃ {u : W // u ∈ finiteOutside e})
    (hFibre : ∀ (i : Fin s) (b c : Fin t),
      SameClosedNeighbourhood H (label (i,b)).val (label (i,c)).val)
    (hOutside : (outsideInducedGraph H e).comap label = cliqueUnion s t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (i j : Fin s) :
    (zeroPartialOutsideMask H e anchor label i).card =
      (zeroPartialOutsideMask H e anchor label j).card := by
  classical
  let phi : CoverVertex s t ≃ W := balancedHostEquiv e label
  have hTrans : HasTransitiveGraphAutomorphisms (H.comap phi) :=
    transitive_comap_equiv H phi hTransitive
  letI : Nonempty (CoverVertex s t) :=
    ⟨(false,(⟨0,hs⟩,anchor))⟩
  obtain ⟨d,hReg⟩ :=
    regular_of_transitive_graph (H.comap phi) hTrans
  have hEqGraph :
      H.comap phi = maskCoverGraph s t
        (zeroPartialOutsideMask H e anchor label) :=
    zero_partial_host_eq_maskCoverGraph
      H e he hNoPartial anchor label hFibre hOutside
  have hRegMask :
      (maskCoverGraph s t
        (zeroPartialOutsideMask H e anchor label)).IsRegularOfDegree d := by
    intro v
    have hNeighbours :
        (maskCoverGraph s t
          (zeroPartialOutsideMask H e anchor label)).neighborFinset v =
          (H.comap phi).neighborFinset v := by
      ext u
      simp only [SimpleGraph.mem_neighborFinset]
      have hAdj :=
        congrArg
          (fun G : SimpleGraph (CoverVertex s t) => G.Adj v u)
          hEqGraph
      exact Iff.of_eq hAdj.symm
    change
      ((maskCoverGraph s t
        (zeroPartialOutsideMask H e anchor label)).neighborFinset v).card = d
    rw [hNeighbours]
    exact hReg v
  exact maskCoverGraph_regular_forces_equal_mask_cards
    (zeroPartialOutsideMask H e anchor label) ht hRegMask i j

end EPPAIII.CliqueCovers
