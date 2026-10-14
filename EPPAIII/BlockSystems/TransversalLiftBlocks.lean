import EPPAIII.BlockSystems.OccupiedBlockAction

/-!
# Partial automorphisms of complete occupied-block transversals

Suppose a partial automorphism of the distinguished induced G is
defined on a set D meeting every occupied host block. Any genuine
EPPA extension permutes the occupied block labels amongst themselves:
the image of the representative from each occupied block is a
selected vertex, and the induced block permutation is bijective.

No coherence of extensions, natural action on all of G, or
pre-existing partition of the outside vertices is assumed.

In particular, if exactly one host block U is unoccupied then
every such EPPA lift fixes U as a block. This is the action
invariant needed in the remaining part of Claim 3.15.
-/

namespace EPPAIII.BlockSystems

/-- An EPPA extension whose domain meets every selected block
induces a permutation that preserves the *set* of occupied block
labels, even when the extension is not coherent across different
partial automorphisms. -/
theorem eppa_transversal_lift_preserves_occupied {V W B : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (D : Finset V)
    (hHits : ∀ b ∈ occupiedBlocks e block,
      ∃ x ∈ D, block (e x) = b)
    (p : Equiv.Perm V)
    (hpPartial : IsPartialGraphAutomorphism G D p) :
    ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q),
      (∀ b : B, b ∈ occupiedBlocks e block ↔
        (liftBlockAutomorphism H block hBlocks hSurj q hq) b ∈
          occupiedBlocks e block) ∧
      (∀ x : V, x ∈ D → q (e x) = e (p x)) := by
  classical
  obtain ⟨q,hq,hExt⟩ := heppa.2 D p hpPartial
  let S : Finset B := occupiedBlocks e block
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  have hMap (b : B) (hb : b ∈ S) : σ b ∈ S := by
    obtain ⟨x,hx,hbx⟩ := hHits b hb
    have hσb : σ b = block (e (p x)) := by
      calc
        σ b = σ (block (e x)) := congrArg σ hbx.symm
        _ = block (q (e x)) :=
          liftBlockAutomorphism_vertex
            H block hBlocks hSurj q hq (e x)
        _ = block (e (p x)) := congrArg block (hExt x hx)
    exact (mem_occupiedBlocks e block (σ b)).mpr
      ⟨p x, hσb.symm⟩
  have hImageSubset : S.image σ ⊆ S := by
    intro b hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
    rw [← hab]
    exact hMap a ha
  have hImageCard : (S.image σ).card = S.card :=
    Finset.card_image_of_injective S σ.injective
  have hImageEq : S.image σ = S :=
    Finset.eq_of_subset_of_card_le hImageSubset
      (by rw [hImageCard])
  have hBack (b : B) (hb : σ b ∈ S) : b ∈ S := by
    have hbImage : σ b ∈ S.image σ := by
      rw [hImageEq]
      exact hb
    obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hbImage
    have hab' : a = b := σ.injective hab
    simpa [hab'] using ha
  refine ⟨q,hq,?_,hExt⟩
  intro b
  constructor
  · exact hMap b
  · exact hBack b

/-- Every full-transversal EPPA extension fixes the unique block
disjoint from the selected copy (as a block label). -/
theorem eppa_transversal_lift_fixes_unique_unoccupied {V W B : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (U : B) (hU : U ∉ occupiedBlocks e block)
    (hOnly : ∀ b : B, b ∉ occupiedBlocks e block → b = U)
    (D : Finset V)
    (hHits : ∀ b ∈ occupiedBlocks e block,
      ∃ x ∈ D, block (e x) = b)
    (p : Equiv.Perm V)
    (hpPartial : IsPartialGraphAutomorphism G D p) :
    ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q),
      (liftBlockAutomorphism H block hBlocks hSurj q hq) U = U ∧
      (∀ x : V, x ∈ D → q (e x) = e (p x)) := by
  obtain ⟨q,hq,hPreserves,hExt⟩ :=
    eppa_transversal_lift_preserves_occupied
      G H e heppa block hBlocks hSurj D hHits p hpPartial
  have hOutside :
      (liftBlockAutomorphism H block hBlocks hSurj q hq) U ∉
        occupiedBlocks e block := by
    intro hb
    exact hU ((hPreserves U).mpr hb)
  exact ⟨q,hq,hOnly _ hOutside,hExt⟩

end EPPAIII.BlockSystems
