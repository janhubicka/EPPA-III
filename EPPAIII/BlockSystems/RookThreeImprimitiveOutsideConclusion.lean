import EPPAIII.BlockSystems.RookThreeTwoPointBlockOutside
import EPPAIII.BlockSystems.RookThreeNineBlockOutside
import EPPAIII.BlockSystems.RookThreeComplementIso

/-!
# Claim 6.16: the outside graph of an imprimitive R3 EPPA host

This is the actual-host assembly for every nontrivial invariant
partition. The selected rook automorphism action is primitive,
so the host blocks have size 2 or 9. The size-nine case is
transported by one genuine host automorphism. In size two,
EPPA constructs canonical pairs and forces the outside graph to
be rook or anti-rook; an explicit finite complement isomorphism
reduces both to rook.

No pre-labelled outside half, coherent EPPA lift, or external
homogeneous/rank-three classification is used.
-/

namespace EPPAIII.BlockSystems

/-- Turn a fixed-bottom equivalence Bool×R3 ≃ W into an
equivalence from the rook base onto the actual complementary
half, without introducing any additional choice. -/
private theorem rook_outside_equiv_from_fixed_bottom
    {W : Type*} [Fintype W]
    (e : rookVertex ↪ W) (h18 : Fintype.card W = 18)
    (φ : Bool × rookVertex ≃ W)
    (hBottom : ∀ x : rookVertex, φ (false,x) = e x) :
    ∃ f : rookVertex ≃ {w : W // w ∈ finiteOutside e},
      ∀ x : rookVertex, (f x).val = φ (true,x) := by
  classical
  have hOut (x : rookVertex) : φ (true,x) ∈ finiteOutside e := by
    have hNot : φ (true,x) ∉ Set.range e := by
      rintro ⟨y,hy⟩
      have hSame : (false,y) = (true,x) :=
        φ.injective (by
          calc
            φ (false,y) = e y := hBottom y
            _ = φ (true,x) := hy)
      exact Bool.false_ne_true (congrArg Prod.fst hSame)
    simpa [finiteOutside] using hNot
  let F : rookVertex →
      {w : W // w ∈ finiteOutside e} :=
    fun x => ⟨φ (true,x),hOut x⟩
  have hInj : Function.Injective F := by
    intro x y hxy
    exact congrArg Prod.snd
      (φ.injective (congrArg Subtype.val hxy))
  have hOutsideCard :
      Fintype.card rookVertex =
        Fintype.card {w : W // w ∈ finiteOutside e} := by
    have hSize := finiteOutside_card e
    rw [h18] at hSize
    rw [Fintype.card_coe]
    have hRook : Fintype.card rookVertex = 9 := by decide
    omega
  let f : rookVertex ≃ {w : W // w ∈ finiteOutside e} :=
    Equiv.ofBijective F
      ((Fintype.bijective_iff_injective_and_card F).mpr
        ⟨hInj,hOutsideCard⟩)
  exact ⟨f,by intro x; rfl⟩

/-- The full current Claim 6.16, with precisely the actual
imprimitive host hypotheses. The outside induced graph is
canonically identified with R3, not merely one of two
unnamed orbit-invariant graph types. -/
theorem rook_eppa_imprimitive_outside_is_rook
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
    ∃ f : rookVertex ≃ {w : W // w ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = rookThreeGraph := by
  classical
  rcases rook_eppa_nontrivial_imprimitive_block_sizes
      H e heppa block hBlocks hSurj hTrans
      h18 hMany hNontrivial with hTwo | hNine
  · have hInject : Function.Injective (fun x : rookVertex =>
        block (e x)) := by
      rcases rook_eppa_selected_block_transversal_or_single
          H e heppa block hBlocks with hInj | hAll
      · exact hInj
      · exfalso
        let bSel : B := block (e (0,0))
        have hSub :
            ((Finset.univ : Finset rookVertex).image e) ⊆
              ((Finset.univ : Finset W).filter
                (fun w => block w = bSel)) := by
          intro w hw
          obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hw
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _,by
              rw [← hx]
              exact hAll x (0,0)⟩
        have hImageCard :
            ((Finset.univ : Finset rookVertex).image e).card = 9 := by
          have h :=
            Finset.card_image_of_injective
              (Finset.univ : Finset rookVertex) e.injective
          simpa [rookVertex] using h
        have hBound := Finset.card_le_card hSub
        rw [hImageCard,hTwo bSel] at hBound
        omega
    obtain ⟨φ,hBottom,hTop⟩ :=
      rook_eppa_two_point_blocks_outside_graph_two_forms
        H e heppa hTrans block hBlocks hInject hTwo h18
    obtain ⟨f,hTopVal⟩ :=
      rook_outside_equiv_from_fixed_bottom e h18 φ hBottom
    have hTopGraph :
        H.comap (fun x => (f x).val) =
          CliqueCovers.sideGraph (H.comap φ) true := by
      apply SimpleGraph.ext
      funext x y
      apply propext
      change H.Adj (f x).val (f y).val ↔
        H.Adj (φ (true,x)) (φ (true,y))
      rw [hTopVal x,hTopVal y]
    rcases hTop with hRook | hComplement
    · exact ⟨f,by rw [hTopGraph,hRook]⟩
    · let f' : rookVertex ≃ {w : W // w ∈ finiteOutside e} :=
        rookComplementIndex.trans f
      refine ⟨f',?_⟩
      have hCompose :
          H.comap (fun x => (f' x).val) =
            (H.comap (fun x => (f x).val)).comap
              rookComplementIndex := by
        apply SimpleGraph.ext
        funext x y
        rfl
      rw [hCompose,hTopGraph,hComplement]
      exact rookComplementIndex_comap_back
  · exact rook_eppa_nine_block_outside_is_rook
      H e heppa block hBlocks hTrans h18 hNine

end EPPAIII.BlockSystems
