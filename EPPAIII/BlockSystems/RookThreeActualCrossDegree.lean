import EPPAIII.BlockSystems.RookThreeImprimitiveOutsideConclusion
import EPPAIII.BlockSystems.RookThreeUniformCrossDegree

/-!
# The actual uniform cross-degree of imprimitive R3 EPPA hosts

Claim 6.16 gives a genuine outside-half equivalence with R3.
Transitivity of the full host then implies that all vertices
of the outside half have the same number of neighbours in the
selected R3. This follows from the identical internal degree
four on both halves, not from an assumed outside group action.

This is the main bridge between the actual imprimitivity
hypotheses and the previously formalized R3 orbit-multiplicity
classification of cross degrees 0 through 4.
-/

namespace EPPAIII.BlockSystems

theorem rook_eppa_imprimitive_uniform_cross_degree
    {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (h18 : Fintype.card W = 18)
    (hMany : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card) :
    ∃ k : ℕ, k ≤ 9 ∧
      ∀ w : W, w ∈ finiteOutside e →
        (finiteNeighbourhoodProfile H e w).card = k := by
  classical
  obtain ⟨f,hOutside⟩ :=
    rook_eppa_imprimitive_outside_is_rook
      H e heppa block hBlocks hSurj hTrans
      h18 hMany hNontrivial
  let phi : Bool × rookVertex ≃ W :=
    CliqueCovers.balancedHostEquiv e f
  have hTrans' :
      CliqueCovers.HasTransitiveGraphAutomorphisms (H.comap phi) :=
    CliqueCovers.transitive_comap_equiv H phi hTrans
  have hTop : CliqueCovers.sideGraph (H.comap phi) true =
      rookThreeGraph := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change (H.comap (fun z : rookVertex => (f z).val)).Adj x y ↔
      rookThreeGraph.Adj x y
    rw [hOutside]
  obtain ⟨k,hk,hRows⟩ :=
    rook_paired_outside_uniform_cross_degree
      (H.comap phi) hTrans' (Or.inl hTop)
  have hProfile (x : rookVertex) :
      finiteNeighbourhoodProfile H e (f x).val =
        (Finset.univ : Finset rookVertex).filter
          (fun y => (H.comap phi).Adj (true,x) (false,y)) := by
    ext y
    simp only [finiteNeighbourhoodProfile,Finset.mem_filter,
      Finset.mem_univ,true_and]
    change H.Adj (f x).val (e y) ↔
      H.Adj (phi (true,x)) (phi (false,y))
    rfl
  have hRowCard (x : rookVertex) :
      (finiteNeighbourhoodProfile H e (f x).val).card =
        rookOutsideCrossDegree (H.comap phi) x := by
    rw [hProfile x]
    unfold rookOutsideCrossDegree
    simpa using (Finset.sum_boole
      (p := fun y : rookVertex =>
        (H.comap phi).Adj (true,x) (false,y))
      (s := Finset.univ) (R := ℕ)).symm
  refine ⟨k,hk,?_⟩
  intro w hw
  let x : rookVertex := f.symm ⟨w,hw⟩
  have hfx : (f x).val = w := by
    simp [x]
  rw [←hfx, hRowCard x]
  exact hRows x

end EPPAIII.BlockSystems
