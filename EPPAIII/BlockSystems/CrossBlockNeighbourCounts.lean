import EPPAIII.BlockSystems.TransversalLiftBlocks
import EPPAIII.BlockSystems.UnequalCliqueBaseBlocks
import EPPAIII.DoubleCover.TwoPointAction

/-!
# Per-block neighbour counts under genuine two-point EPPA

Count the neighbours of a host vertex u in an indicated invariant
block b. A genuine host automorphism preserves this count when it
transports both u and b.

If two ordered selected pairs (x,z), (y,w) belong to distinct
invariant blocks, then both pairs are nonedges in the selected
graph. Two-point EPPA produces an actual host automorphism mapping
e(x) to e(y) and e(z) to e(w). Its induced permutation transports
the target block, so the per-block neighbour counts agree.

No transversal construction or coherent action is required at
this stage. This is the fundamental cross-degree uniformity input
for Claim 3.15.
-/

namespace EPPAIII.BlockSystems

/-- The number of neighbours of u in an invariant block b. -/
noncomputable def neighboursInBlock {W B : Type*}
    [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (block : W → B) (u : W) (b : B) : ℕ := by
  exact ((Finset.univ : Finset W).filter
    (fun v => block v = b ∧ H.Adj u v)).card

/-- A graph automorphism that preserves the block system
transports the number of neighbours in each block. -/
theorem neighboursInBlock_aut {W B : Type*}
    [Fintype W] [DecidableEq W] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
    (u : W) (b : B) :
    neighboursInBlock H block u b =
      neighboursInBlock H block (q u)
        (liftBlockAutomorphism H block hBlocks hSurj q hq b) := by
  classical
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  let S : Finset W := (Finset.univ : Finset W).filter
    (fun v => block v = b ∧ H.Adj u v)
  let T : Finset W := (Finset.univ : Finset W).filter
    (fun v => block v = σ b ∧ H.Adj (q u) v)
  have hImage : S.image q = T := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,hv,hvw⟩ := Finset.mem_image.mp hw
      have hvParts : block v = b ∧ H.Adj u v :=
        (Finset.mem_filter.mp hv).2
      have hBlock : block w = σ b := by
        rw [← hvw]
        calc
          block (q v) = σ (block v) :=
            (liftBlockAutomorphism_vertex
              H block hBlocks hSurj q hq v).symm
          _ = σ b := by rw [hvParts.1]
      have hAdj : H.Adj (q u) w := by
        rw [← hvw]
        exact (hq u v).mp hvParts.2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,⟨hBlock,hAdj⟩⟩
    · intro hw
      have hwParts : block w = σ b ∧ H.Adj (q u) w :=
        (Finset.mem_filter.mp hw).2
      apply Finset.mem_image.mpr
      refine ⟨q.symm w, ?_, ?_⟩
      · have hBlock : block (q.symm w) = b := by
          apply σ.injective
          calc
            σ (block (q.symm w)) = block (q (q.symm w)) :=
              liftBlockAutomorphism_vertex
                H block hBlocks hSurj q hq (q.symm w)
            _ = block w := by simp
            _ = σ b := hwParts.1
        have hAdj : H.Adj u (q.symm w) := by
          apply (hq u (q.symm w)).mpr
          simpa using hwParts.2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,⟨hBlock,hAdj⟩⟩
      · exact q.apply_symm_apply w
  calc
    neighboursInBlock H block u b = S.card := rfl
    _ = (S.image q).card :=
      (Finset.card_image_of_injective _ q.injective).symm
    _ = T.card := congrArg Finset.card hImage
    _ = neighboursInBlock H block (q u) (σ b) := rfl

/-- Two-point EPPA identifies the neighbour counts from a
selected vertex into any other occupied block. -/
theorem eppa_selected_block_neighbour_count_eq {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hSame : ∀ a b : V,
      block (e a) = block (e b) ↔ a = b ∨ G.Adj a b)
    (x z y w : V)
    (hxz : block (e x) ≠ block (e z))
    (hyw : block (e y) ≠ block (e w)) :
    neighboursInBlock H block (e x) (block (e z)) =
      neighboursInBlock H block (e y) (block (e w)) := by
  classical
  have hXZ : x ≠ z := by
    intro h
    exact hxz (congrArg (fun v : V => block (e v)) h)
  have hYW : y ≠ w := by
    intro h
    exact hyw (congrArg (fun v : V => block (e v)) h)
  have hNonXZ : ¬ G.Adj x z := by
    intro h
    exact hxz ((hSame x z).mpr (Or.inr h))
  have hNonYW : ¬ G.Adj y w := by
    intro h
    exact hyw ((hSame y w).mpr (Or.inr h))
  have hType : G.Adj x z ↔ G.Adj y w :=
    ⟨fun h => False.elim (hNonXZ h),
      fun h => False.elim (hNonYW h)⟩
  obtain ⟨p,hpx,hpz,hPartial⟩ :=
    DoubleCover.partial_of_two_maps G x z y w hXZ hYW hType
  obtain ⟨q,hq,hExt⟩ := heppa.2 ({x,z} : Finset V) p hPartial
  have hqx : q (e x) = e y := by
    simpa [hpx] using hExt x (by simp)
  have hqz : q (e z) = e w := by
    simpa [hpz] using hExt z (by simp)
  have hσz :
      liftBlockAutomorphism H block hBlocks hSurj q hq (block (e z)) =
        block (e w) := by
    calc
      liftBlockAutomorphism H block hBlocks hSurj q hq (block (e z)) =
          block (q (e z)) :=
        liftBlockAutomorphism_vertex H block hBlocks hSurj q hq (e z)
      _ = block (e w) := by rw [hqz]
  have hCount := neighboursInBlock_aut
    H block hBlocks hSurj q hq (e x) (block (e z))
  simpa only [hqx,hσz] using hCount

end EPPAIII.BlockSystems
