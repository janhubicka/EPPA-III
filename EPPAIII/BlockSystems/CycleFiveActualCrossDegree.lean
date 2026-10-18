import EPPAIII.BlockSystems.CycleFiveUniformCrossDegree
import EPPAIII.BlockSystems.CycleFiveEmptyFullConclusion

/-!
# Uniform cross-degree for actual ten-vertex C5 EPPA witnesses

The outside induced graph is known to be C5 under a genuine
equivalence. Transport the host to two labelled halves and use
vertex-transitivity plus the degree-two property of both cycles.
This gives a common cross-degree k ≤ 5 on every actual outside
vertex, without assuming imprimitivity or any outside action.
-/

namespace EPPAIII.BlockSystems

theorem cycleFive_eppa_actual_uniform_cross_degree
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10) :
    ∃ k : ℕ, k ≤ 5 ∧
      ∀ w : W, w ∈ finiteOutside e →
        (finiteNeighbourhoodProfile H e w).card = k := by
  classical
  obtain ⟨f,hOutside⟩ :=
    cycleFive_eppa_outside_is_cycle H e heppa hTrans hTen
  let phi : Bool × Fin 5 ≃ W :=
    CliqueCovers.balancedHostEquiv e f
  have hTrans' :
      CliqueCovers.HasTransitiveGraphAutomorphisms (H.comap phi) :=
    CliqueCovers.transitive_comap_equiv H phi hTrans
  have hTop : CliqueCovers.sideGraph (H.comap phi) true =
      SimpleGraph.cycleGraph 5 := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change (H.comap (fun z : Fin 5 => (f z).val)).Adj x y ↔
      (SimpleGraph.cycleGraph 5).Adj x y
    rw [hOutside]
  obtain ⟨k,hk,hRows⟩ :=
    cycleFive_paired_outside_uniform_cross_degree
      (H.comap phi) hTrans' hTop
  have hProfile (x : Fin 5) :
      finiteNeighbourhoodProfile H e (f x).val =
        (Finset.univ : Finset (Fin 5)).filter
          (fun y => (H.comap phi).Adj (true,x) (false,y)) := by
    ext y
    simp only [finiteNeighbourhoodProfile,Finset.mem_filter,
      Finset.mem_univ,true_and]
    change H.Adj (f x).val (e y) ↔
      H.Adj (phi (true,x)) (phi (false,y))
    rfl
  have hRowCard (x : Fin 5) :
      (finiteNeighbourhoodProfile H e (f x).val).card =
        cycleFiveOutsideCrossDegree (H.comap phi) x := by
    rw [hProfile x]
    unfold cycleFiveOutsideCrossDegree
    simpa using (Finset.sum_boole
      (p := fun y : Fin 5 =>
        (H.comap phi).Adj (true,x) (false,y))
      (s := Finset.univ) (R := ℕ)).symm
  refine ⟨k,hk,?_⟩
  intro w hw
  let x : Fin 5 := f.symm ⟨w,hw⟩
  have hfx : (f x).val = w := by
    simp [x]
  rw [←hfx, hRowCard x]
  exact hRows x

end EPPAIII.BlockSystems
