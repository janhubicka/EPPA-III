import EPPAIII.BlockSystems.TransitiveSeparatedHalf
import EPPAIII.BlockSystems.TransitivePartition

/-!
# Transporting a filled invariant half to the outside half

A vertex-transitive host with twice the selected order has the
same induced graph on the outside half whenever the selected
copy fills one invariant imprimitivity block. No separation of
the two halves by missing cross-edges is required.

This is the size-nine-block branch of the R3 exceptional lemma.
The proof chooses a *single actual host automorphism* taking one
selected vertex outside. Invariance transports its entire filled
block outside, giving the required graph equivalence.
-/

namespace EPPAIII.BlockSystems

/-- When the selected G occupies exactly one invariant host
block, vertex transitivity transports this graph onto the full
complementary half. Edges between the two blocks may be arbitrary. -/
theorem transitive_outside_equiv_of_filled_invariant_half
    {V W B : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (he : IsInducedGraphEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (b₀ : B)
    (hSelected : ∀ x : V, block (e x) = b₀)
    (hFilled : ∀ w : W, block w = b₀ → ∃ x : V, e x = w)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hTrans : IsVertexTransitive H) :
    ∃ f : V ≃ {w : W // w ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = G := by
  classical
  have hOutsideCard : (finiteOutside e).card = Fintype.card V := by
    rw [finiteOutside_card,hDouble]
    omega
  have hOutsidePositive : 0 < (finiteOutside e).card := by
    rw [hOutsideCard]
    exact Fintype.card_pos
  obtain ⟨w,hw⟩ := Finset.card_pos.mp hOutsidePositive
  have hBlockOutside : block w ≠ b₀ := by
    intro hwBlock
    obtain ⟨x,hx⟩ := hFilled w hwBlock
    have hwNoRange : w ∉ Set.range e := by
      simpa [finiteOutside] using hw
    exact hwNoRange ⟨x,hx⟩
  let x₀ : V := Classical.choice inferInstance
  obtain ⟨q,hq,hqw⟩ := hTrans (e x₀) w
  have hImageOutside (x : V) : q (e x) ∈ finiteOutside e := by
    have hEqual : block (e x) = block (e x₀) :=
      (hSelected x).trans (hSelected x₀).symm
    have hAfter :=
      (hBlocks q hq (e x) (e x₀)).mp hEqual
    rw [hqw] at hAfter
    have hNoRange : q (e x) ∉ Set.range e := by
      rintro ⟨y,hy⟩
      have hInBlock : block (q (e x)) = b₀ := by
        rw [← hy]
        exact hSelected y
      exact hBlockOutside (hAfter.symm.trans hInBlock)
    simpa [finiteOutside] using hNoRange
  let f : V → {w : W // w ∈ finiteOutside e} :=
    fun x => ⟨q (e x),hImageOutside x⟩
  have hfInj : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply q.injective
    exact congrArg Subtype.val hxy
  have hCard :
      Fintype.card V =
        Fintype.card {w : W // w ∈ finiteOutside e} := by
    rw [Fintype.card_coe]
    exact hOutsideCard.symm
  let φ : V ≃ {w : W // w ∈ finiteOutside e} :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr
        ⟨hfInj,hCard⟩)
  refine ⟨φ,?_⟩
  apply SimpleGraph.ext
  funext x y
  apply propext
  calc
    H.Adj (φ x).val (φ y).val ↔
        H.Adj (q (e x)) (q (e y)) := Iff.rfl
    _ ↔ H.Adj (e x) (e y) := (hq (e x) (e y)).symm
    _ ↔ G.Adj x y := (he x y).symm

end EPPAIII.BlockSystems
