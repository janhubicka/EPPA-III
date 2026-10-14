import EPPAIII.BlockSystems.TransversalLiftBlocks
import EPPAIII.BlockSystems.Case1UnoccupiedBound

/-!
# Unoccupied-block obstruction via neighbourhood support

For a block U disjoint from the selected copy, record which host
vertices have a neighbour in U. If every selected vertex has such a
neighbour, Claim 3.14 shows that this support, restricted to any
occupied block B, is exactly the selected vertices in B.

Automorphisms preserving U preserve the support. Thus an automorphism
sending a selected vertex in B to one in C, while fixing U, forces
the selected cardinalities of B and C to agree.

The final theorem below assumes the existence of these fixed-U
automorphisms for every ordered pair of selected vertices. The
separate EPPA transversal lemma is the intended way to produce them;
this file does not silently postulate coherent EPPA lifts.
-/

namespace EPPAIII.BlockSystems

/-- A host vertex has a neighbour in the specified invariant block. -/
def TouchesBlock {W B : Type*}
    (H : SimpleGraph W) (block : W → B) (U : B) (w : W) : Prop :=
  ∃ z : W, block z = U ∧ H.Adj w z

/-- An automorphism preserving the distinguished block preserves
the predicate of having a neighbour in it. -/
theorem touchesBlock_aut_iff {W B : Type*}
    (H : SimpleGraph W) (block : W → B) (U : B)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
    (hFixU : ∀ z : W, block z = U ↔ block (q z) = U)
    (w : W) :
    TouchesBlock H block U w ↔
      TouchesBlock H block U (q w) := by
  constructor
  · rintro ⟨z,hz,hAdj⟩
    exact ⟨q z,(hFixU z).mp hz,(hq w z).mp hAdj⟩
  · rintro ⟨z,hz,hAdj⟩
    refine ⟨q.symm z, ?_, ?_⟩
    · apply (hFixU (q.symm z)).mpr
      simpa using hz
    · apply (hq w (q.symm z)).mpr
      simpa using hAdj

/-- The vertices in the block b with some neighbour in U. -/
noncomputable def touchedInBlock {W B : Type*}
    [Fintype W]
    (H : SimpleGraph W) (block : W → B) (U b : B) : Finset W := by
  classical
  exact Finset.univ.filter (fun w =>
    block w = b ∧ TouchesBlock H block U w)

/-- If U contains no selected vertex, there are no outside-to-U
cross-block edges, and all selected vertices touch U, the touching
vertices in any different block are precisely its selected points. -/
theorem touchedInBlock_eq_selected_image {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) (e : V ↪ W) (block : W → B)
    (U b : B) (hU : U ∉ occupiedBlocks e block) (hbU : b ≠ U)
    (hSelectedTouch : ∀ x : V, TouchesBlock H block U (e x))
    (hNoOutsideCross : ∀ w z : W,
      w ∉ Set.range e → z ∉ Set.range e →
      H.Adj w z → block w = block z) :
    touchedInBlock H block U b = (selectedInBlock e block b).image e := by
  classical
  ext w
  constructor
  · intro hw
    have hwParts :
        block w = b ∧ TouchesBlock H block U w :=
      (Finset.mem_filter.mp hw).2
    obtain ⟨z,hzU,hAdj⟩ := hwParts.2
    have hzOutside : z ∉ Set.range e := by
      rintro ⟨x,hx⟩
      apply hU
      apply (mem_occupiedBlocks e block U).mpr
      exact ⟨x, by rw [hx]; exact hzU⟩
    have hwSelected : w ∈ Set.range e := by
      by_contra hwOutside
      have hSame := hNoOutsideCross w z hwOutside hzOutside hAdj
      exact hbU (hwParts.1.symm.trans (hSame.trans hzU))
    obtain ⟨x,hx⟩ := hwSelected
    refine Finset.mem_image.mpr ⟨x, ?_, hx⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rw [hx]; exact hwParts.1⟩
  · intro hw
    obtain ⟨x,hx,hxw⟩ := Finset.mem_image.mp hw
    have hxBlock : block (e x) = b :=
      (Finset.mem_filter.mp hx).2
    have hwBlock : block w = b := by
      rw [← hxw]
      exact hxBlock
    have hwTouch : TouchesBlock H block U w := by
      rw [← hxw]
      exact hSelectedTouch x
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨hwBlock,hwTouch⟩⟩

/-- The support in an occupied block has exactly that block's
selected occupancy size. -/
theorem touchedInBlock_card_eq_selected {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) (e : V ↪ W) (block : W → B)
    (U b : B) (hU : U ∉ occupiedBlocks e block) (hbU : b ≠ U)
    (hSelectedTouch : ∀ x : V, TouchesBlock H block U (e x))
    (hNoOutsideCross : ∀ w z : W,
      w ∉ Set.range e → z ∉ Set.range e →
      H.Adj w z → block w = block z) :
    (touchedInBlock H block U b).card =
      (selectedInBlock e block b).card := by
  classical
  rw [touchedInBlock_eq_selected_image H e block U b
    hU hbU hSelectedTouch hNoOutsideCross]
  exact Finset.card_image_of_injective _ e.injective

/-- A block-preserving graph automorphism transports touching
vertices from one indicated block to its image. -/
theorem touchedInBlock_image_aut {W B : Type*}
    [Fintype W]
    (H : SimpleGraph W) (block : W → B) (U b c : B)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
    (hFixU : ∀ w : W, block w = U ↔ block (q w) = U)
    (hBC : ∀ w : W, block w = b ↔ block (q w) = c) :
    (touchedInBlock H block U b).image q =
      touchedInBlock H block U c := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨z,hz,hzw⟩ := Finset.mem_image.mp hw
    have hParts : block z = b ∧ TouchesBlock H block U z :=
      (Finset.mem_filter.mp hz).2
    have hBlock : block w = c := by
      rw [← hzw]
      exact (hBC z).mp hParts.1
    have hTouches : TouchesBlock H block U w := by
      rw [← hzw]
      exact (touchesBlock_aut_iff H block U q hq hFixU z).mp hParts.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨hBlock,hTouches⟩⟩
  · intro hw
    have hParts : block w = c ∧ TouchesBlock H block U w :=
      (Finset.mem_filter.mp hw).2
    refine Finset.mem_image.mpr ⟨q.symm w, ?_, by simp⟩
    have hb : block (q.symm w) = b := by
      apply (hBC (q.symm w)).mpr
      simpa using hParts.1
    have hTouch : TouchesBlock H block U (q.symm w) := by
      apply (touchesBlock_aut_iff H block U q hq hFixU (q.symm w)).mpr
      simpa using hParts.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,⟨hb,hTouch⟩⟩

/-- If all selected vertices can be moved to one another by
genuine host automorphisms stabilizing a block U, then the
block U cannot be unoccupied in a complete block-connection
graph with unequal selected occupancy sizes. -/
theorem no_unoccupied_block_of_fixedU_selected_transitivity {V W B : Type*}
    [Fintype V] [Nonempty V] [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) (e : V ↪ W) (block : W → B)
    (U : B) (hU : U ∉ occupiedBlocks e block)
    (hComplete : blockConnectionGraph H block = ⊤)
    (hNoOutsideCross : ∀ w z : W,
      w ∉ Set.range e → z ∉ Set.range e →
      H.Adj w z → block w = block z)
    (hBlocks : InvariantBlockMap H block)
    (hFixedLifts : ∀ x y : V,
      ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q),
        q (e x) = e y ∧
        (∀ z : W, block z = U ↔ block (q z) = U))
    (b c : B) (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    False := by
  classical
  let origin : V := Classical.choice inferInstance
  let b₀ : B := block (e origin)
  have hb₀U : b₀ ≠ U := by
    intro h
    apply hU
    exact (mem_occupiedBlocks e block U).mpr ⟨origin,h⟩
  have hEdge : (blockConnectionGraph H block).Adj b₀ U := by
    rw [hComplete]
    exact hb₀U
  obtain ⟨_,w,z,hwB,hzU,hAdj⟩ := hEdge
  have hzOutside : z ∉ Set.range e := by
    rintro ⟨x,hx⟩
    apply hU
    exact (mem_occupiedBlocks e block U).mpr
      ⟨x,by rw [hx]; exact hzU⟩
  have hwSelected : w ∈ Set.range e := by
    by_contra hwOutside
    have hSame := hNoOutsideCross w z hwOutside hzOutside hAdj
    exact hb₀U (hwB.symm.trans (hSame.trans hzU))
  obtain ⟨x₀,hx₀⟩ := hwSelected
  have hFirstTouch : TouchesBlock H block U (e x₀) := by
    rw [hx₀]
    exact ⟨z,hzU,hAdj⟩
  have hSelectedTouch (x : V) : TouchesBlock H block U (e x) := by
    obtain ⟨q,hq,hMap,hFixU⟩ := hFixedLifts x₀ x
    have h := (touchesBlock_aut_iff H block U q hq hFixU (e x₀)).mp
      hFirstTouch
    rw [hMap] at h
    exact h
  obtain ⟨x,hx⟩ := (mem_occupiedBlocks e block b).mp hb
  obtain ⟨y,hy⟩ := (mem_occupiedBlocks e block c).mp hc
  obtain ⟨q,hq,hMap,hFixU⟩ := hFixedLifts x y
  have hBC (w : W) : block w = b ↔ block (q w) = c := by
    constructor
    · intro hw
      have hSame : block w = block (e x) := hw.trans hx.symm
      have hTransport := (hBlocks q hq w (e x)).mp hSame
      simpa only [hMap,hy] using hTransport
    · intro hw
      have hTransport : block (q w) = block (q (e x)) := by
        simpa only [hMap,hy] using hw
      exact ((hBlocks q hq w (e x)).mpr hTransport).trans hx
  have hbU : b ≠ U := by
    intro h
    exact hU (by simpa [h] using hb)
  have hcU : c ≠ U := by
    intro h
    exact hU (by simpa [h] using hc)
  have hBcard := touchedInBlock_card_eq_selected
    H e block U b hU hbU hSelectedTouch hNoOutsideCross
  have hCcard := touchedInBlock_card_eq_selected
    H e block U c hU hcU hSelectedTouch hNoOutsideCross
  have hImage := touchedInBlock_image_aut
    H block U b c q hq hFixU hBC
  have hCards :
      (touchedInBlock H block U b).card =
        (touchedInBlock H block U c).card := by
    calc
      (touchedInBlock H block U b).card =
          ((touchedInBlock H block U b).image q).card :=
        (Finset.card_image_of_injective _ q.injective).symm
      _ = (touchedInBlock H block U c).card := congrArg Finset.card hImage
  exact hDifferent (hBcard.symm.trans (hCards.trans hCcard))

end EPPAIII.BlockSystems
