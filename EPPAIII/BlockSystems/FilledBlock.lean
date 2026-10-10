import EPPAIII.BlockSystems.ClusterObstructions
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# A filled invariant block is itself an EPPA witness

The first claim of Lemma 3.3 uses the following fact:
if all of the selected graph G equals one block of an invariant
partition, any EPPA extension of a nonempty partial automorphism
stabilizes the block and restricts to an automorphism of G.

Here the "fills the block" condition is stated explicitly as
surjectivity of the induced embedding onto that block. Obtaining
this from the host size 2|G| and a nontrivial equal-sized block
partition is the following independent finite counting step.
-/

namespace EPPAIII.BlockSystems

/-- The restriction of an automorphism of the host to a block that
is exactly the selected induced graph supplies an automorphism of G.
This is the missing justification in the manuscript's compressed
"then the block is an EPPA witness" sentence. -/
theorem homogeneous_of_filled_invariant_block {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (b₀ : B)
    (hInside : ∀ x : V, block (e x) = b₀)
    (hFills : ∀ w : W, block w = b₀ → ∃ x : V, e x = w) :
    DoubleCover.IsHomogeneousGraph G := by
  classical
  intro D p hPartial
  by_cases hD : D.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hD
    obtain ⟨q, hq, hExtend⟩ := heppa.2 D p hPartial
    have hTarget : block (q (e x₀)) = b₀ := by
      rw [hExtend x₀ hx₀]
      exact hInside (p x₀)
    have hImagesIn (x : V) : block (q (e x)) = b₀ := by
      have hIn : block (e x) = block (e x₀) :=
        (hInside x).trans (hInside x₀).symm
      exact ((hBlocks q hq (e x) (e x₀)).mp hIn).trans hTarget
    have hImage : ∀ x : V, ∃ y : V, e y = q (e x) :=
      fun x => hFills (q (e x)) (hImagesIn x)
    choose f hf using hImage
    have hInjective : Function.Injective f := by
      intro x y hxy
      apply e.injective
      apply q.injective
      calc
        q (e x) = e (f x) := (hf x).symm
        _ = e (f y) := congrArg e hxy
        _ = q (e y) := hf y
    have hSurjective : Function.Surjective f :=
      Finite.surjective_of_injective hInjective
    let σ : Equiv.Perm V := Equiv.ofBijective f ⟨hInjective, hSurjective⟩
    have hCompat (x : V) : e (σ x) = q (e x) := hf x
    have hAuto : IsGraphAutomorphism G σ := by
      intro x y
      calc
        G.Adj x y ↔ H.Adj (e x) (e y) := heppa.1 x y
        _ ↔ H.Adj (q (e x)) (q (e y)) := hq _ _
        _ ↔ H.Adj (e (σ x)) (e (σ y)) := by
          rw [hCompat x, hCompat y]
        _ ↔ G.Adj (σ x) (σ y) := (heppa.1 (σ x) (σ y)).symm
    refine ⟨σ, hAuto, ?_⟩
    intro x hx
    exact e.injective ((hCompat x).trans (hExtend x hx))
  · refine ⟨Equiv.refl V, ?_, ?_⟩
    · intro x y
      rfl
    · intro x hx
      exact False.elim (hD ⟨x, hx⟩)

end EPPAIII.BlockSystems
