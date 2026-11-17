import EPPAIII.BlockSystems.ImprimitiveGardinerBridge
import EPPAIII.BlockSystems.CycleFiveComplementEppa
import EPPAIII.BlockSystems.RookThreeComplementIso

/-!
# Gardiner's literally stated finite homogeneous graph models

The manuscript states that a finite homogeneous graph is a union of
equal cliques, its complement, C5, the complement of C5, the 3×3 rook
graph, or the complement of that rook graph.

The previous imprimitive assembly uses the normalized four-case form
omitting the last two complements. Here we explicitly justify that
normalization by the already verified self-complementing permutations
of C5 and of the rook graph. Thus the *only* external model assumption
needed is exactly the published six-case Gardiner classification,
not a stronger pre-normalized theorem.

This is a relative formalization: no Gardiner classification theorem
is asserted as a new Lean axiom.
-/

namespace EPPAIII.BlockSystems

/-- The literal six alternatives in Gardiner's classification,
expressed through graph equivalences of the selected finite base. -/
def GardinerPublishedModels {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t) G φ) ∨
  (∃ s t : ℕ, 0 < s ∧ 0 < t ∧
    ∃ φ : (Fin s × Fin t) ≃ V,
      CanonicalBaseCopy (cliqueUnion s t)ᶜ G φ) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G φ) ∨
  (∃ φ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5)ᶜ G φ) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G φ) ∨
  (∃ φ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraphᶜ G φ)

/-- Complementing C5 gives an isomorphic copy via the explicit
multiply-by-two index; the fixed selected model equivalence is
composed with the old one. -/
theorem gardiner_complement_cycle_normalized
    {V : Type*} (G : SimpleGraph V)
    (φ : Fin 5 ≃ V)
    (hModel : CanonicalBaseCopy
      (SimpleGraph.cycleGraph 5)ᶜ G φ) :
    ∃ ψ : Fin 5 ≃ V,
      CanonicalBaseCopy (SimpleGraph.cycleGraph 5) G ψ := by
  let ψ : Fin 5 ≃ V := cycleFiveDoubleIndex.trans φ
  refine ⟨ψ,?_⟩
  intro x y
  have hSelf :
      (SimpleGraph.cycleGraph 5).Adj x y ↔
        ((SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex).Adj x y := by
    rw [cycleFiveComplementIndex_comap_back]
  calc
    (SimpleGraph.cycleGraph 5).Adj x y ↔
        ((SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex).Adj x y :=
      hSelf
    _ ↔ G.Adj (ψ x) (ψ y) := by
      simpa [ψ, Equiv.trans_apply] using
        hModel (cycleFiveDoubleIndex x) (cycleFiveDoubleIndex y)

/-- The rook graph is self-complementary through an explicit
invertible linear change of coordinates over Fin 3. -/
theorem gardiner_complement_rook_normalized
    {V : Type*} (G : SimpleGraph V)
    (φ : rookVertex ≃ V)
    (hModel : CanonicalBaseCopy rookThreeGraphᶜ G φ) :
    ∃ ψ : rookVertex ≃ V,
      CanonicalBaseCopy rookThreeGraph G ψ := by
  let ψ : rookVertex ≃ V := rookComplementIndex.trans φ
  refine ⟨ψ,?_⟩
  intro x y
  have hSelf :
      rookThreeGraph.Adj x y ↔
        (rookThreeGraphᶜ.comap rookComplementIndex).Adj x y := by
    rw [rookComplementIndex_comap_back]
  calc
    rookThreeGraph.Adj x y ↔
        (rookThreeGraphᶜ.comap rookComplementIndex).Adj x y :=
      hSelf
    _ ↔ G.Adj (ψ x) (ψ y) := by
      simpa [ψ, Equiv.trans_apply] using
        hModel (rookComplementIndex x) (rookComplementIndex y)

/-- The literal Gardiner list implies the normalized list
required by the actual-host imprimitive classification. -/
theorem gardiner_published_implies_normalized
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (h : GardinerPublishedModels G) :
    GardinerHomogeneousModels G := by
  rcases h with hEqual | hRest
  · exact Or.inl hEqual
  rcases hRest with hComplement | hRest
  · exact Or.inr (Or.inl hComplement)
  rcases hRest with hCycle | hRest
  · exact Or.inr (Or.inr (Or.inl hCycle))
  rcases hRest with hCycleComplement | hRest
  · obtain ⟨φ,hModel⟩ := hCycleComplement
    obtain ⟨ψ,hψ⟩ :=
      gardiner_complement_cycle_normalized G φ hModel
    exact Or.inr (Or.inr (Or.inl ⟨ψ,hψ⟩))
  rcases hRest with hRook | hRookComplement
  · exact Or.inr (Or.inr (Or.inr hRook))
  · obtain ⟨φ,hModel⟩ := hRookComplement
    obtain ⟨ψ,hψ⟩ :=
      gardiner_complement_rook_normalized G φ hModel
    exact Or.inr (Or.inr (Or.inr ⟨ψ,hψ⟩))

/-- Final source-facing necessity statement, with precisely the
six-case Gardiner premise corresponding to the printed theorem. -/
theorem imprimitive_actual_host_classification_from_published_gardiner
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ DoubleCover.IsHomogeneousGraph H)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hSource : DoubleCover.IsHomogeneousGraph G ∨ IsClusterGraph G)
    (hGardinerPublished : DoubleCover.IsHomogeneousGraph G →
      GardinerPublishedModels G) :
    Fintype.card W = 2 * Fintype.card V ∧
      ImprimitiveHostModels G H e :=
  imprimitive_actual_host_classification_from_gardiner
    G H e heppa block hBlocks hSurj hTrans hNonhomogeneous
    hManyBlocks hNontrivial hBound hSource
    (fun hHom => gardiner_published_implies_normalized
      G (hGardinerPublished hHom))

end EPPAIII.BlockSystems
