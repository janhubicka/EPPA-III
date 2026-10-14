import EPPAIII.BlockSystems.TransitivePartition
import EPPAIII.CliqueCovers.MajorityQuotientRigidity

/-!
# Actual quotient action on an invariant imprimitivity partition

A surjective block map W → B is invariant under every automorphism
of the host. Each genuine host automorphism induces a permutation
of B (without choosing automorphisms coherently across EPPA lifts).
The quotient graph records *existence* of inter-block edges, so
it has no artificial assumption of uniform adjacency between blocks.

If every selected base edge stays inside one block, representatives
in distinct occupied blocks form an independent set. Two-point EPPA
then supplies the required ordered-pair transitivity on those
occupied blocks. This is the previously conditional action input
in the majority-quotient argument for Lemma 3.12, Case 1.
-/

namespace EPPAIII.BlockSystems

/-- Choose a representative for each block of a surjective partition. -/
private noncomputable def blockSection {W B : Type*}
    (block : W → B) (hSurj : Function.Surjective block) (b : B) : W :=
  Classical.choose (hSurj b)

private theorem blockSection_spec {W B : Type*}
    (block : W → B) (hSurj : Function.Surjective block) (b : B) :
    block (blockSection block hSurj b) = b :=
  Classical.choose_spec (hSurj b)

/-- Pointwise action on block labels induced by one actual host
automorphism. Independence of the chosen representative follows
from the invariant equivalence relation. -/
private noncomputable def blockAutMap {W B : Type*}
    (block : W → B) (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (b : B) : B :=
  block (q (blockSection block hSurj b))

private theorem blockAutMap_vertex {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) (w : W) :
    blockAutMap block hSurj q (block w) = block (q w) := by
  unfold blockAutMap
  have hRepresentative :
      block (blockSection block hSurj (block w)) = block w :=
    blockSection_spec block hSurj (block w)
  exact (hBlocks q hq
    (blockSection block hSurj (block w)) w).mp hRepresentative

private theorem blockAutMap_injective {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    Function.Injective (blockAutMap block hSurj q) := by
  intro b c hEqual
  have hSame :=
    (hBlocks q hq
      (blockSection block hSurj b)
      (blockSection block hSurj c)).mpr hEqual
  calc
    b = block (blockSection block hSurj b) :=
      (blockSection_spec block hSurj b).symm
    _ = block (blockSection block hSurj c) := hSame
    _ = c := blockSection_spec block hSurj c

private theorem blockAutMap_surjective {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    Function.Surjective (blockAutMap block hSurj q) := by
  intro b
  refine ⟨block (q.symm (blockSection block hSurj b)), ?_⟩
  rw [blockAutMap_vertex H block hBlocks hSurj q hq]
  simpa using blockSection_spec block hSurj b

/-- The induced action on block labels is a *permutation*, not an
assumption about a quotient group action. -/
noncomputable def liftBlockAutomorphism {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    Equiv.Perm B :=
  Equiv.ofBijective (blockAutMap block hSurj q)
    ⟨blockAutMap_injective H block hBlocks hSurj q hq,
     blockAutMap_surjective H block hBlocks hSurj q hq⟩

/-- On every vertex, the lifted permutation has the expected action. -/
theorem liftBlockAutomorphism_vertex {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) (w : W) :
    liftBlockAutomorphism H block hBlocks hSurj q hq (block w) =
      block (q w) :=
  blockAutMap_vertex H block hBlocks hSurj q hq w

/-- Two distinct blocks are adjacent when at least one edge of H
joins them. We do not assume uniform adjacency across the block pair. -/
def blockConnectionGraph {W B : Type*}
    (H : SimpleGraph W) (block : W → B) : SimpleGraph B where
  Adj := fun a b =>
    a ≠ b ∧ ∃ u v : W, block u = a ∧ block v = b ∧ H.Adj u v
  symm := by
    intro a b h
    obtain ⟨hab,u,v,hu,hv,hadj⟩ := h
    exact ⟨hab.symm,v,u,hv,hu,hadj.symm⟩
  loopless := by
    intro a h
    exact h.1 rfl

/-- The induced block permutation preserves the genuine inter-block
edge-existence graph in both directions. -/
theorem liftBlockAutomorphism_graphAuto {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism (blockConnectionGraph H block)
      (liftBlockAutomorphism H block hBlocks hSurj q hq) := by
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  intro a b
  constructor
  · rintro ⟨hab,u,v,hu,hv,hadj⟩
    refine ⟨σ.injective.ne hab,q u,q v,?_,?_,(hq u v).mp hadj⟩
    · calc
        block (q u) = σ (block u) :=
          (liftBlockAutomorphism_vertex H block hBlocks hSurj q hq u).symm
        _ = σ a := congrArg σ hu
    · calc
        block (q v) = σ (block v) :=
          (liftBlockAutomorphism_vertex H block hBlocks hSurj q hq v).symm
        _ = σ b := congrArg σ hv
  · rintro ⟨hab,u,v,hu,hv,hadj⟩
    have hA : block (q.symm u) = a := by
      apply σ.injective
      calc
        σ (block (q.symm u)) = block (q (q.symm u)) :=
          liftBlockAutomorphism_vertex H block hBlocks hSurj q hq _
        _ = block u := by simp
        _ = σ a := hu
    have hB : block (q.symm v) = b := by
      apply σ.injective
      calc
        σ (block (q.symm v)) = block (q (q.symm v)) :=
          liftBlockAutomorphism_vertex H block hBlocks hSurj q hq _
        _ = block v := by simp
        _ = σ b := hv
    refine ⟨fun h => hab (congrArg σ h),
      q.symm u,q.symm v,hA,hB,?_⟩
    exact (hq (q.symm u) (q.symm v)).mpr (by simpa using hadj)

/-- Host vertex-transitivity descends to the actual graph of blocks. -/
theorem blockConnectionGraph_transitive {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    CliqueCovers.HasTransitiveGraphAutomorphisms
      (blockConnectionGraph H block) := by
  intro a b
  obtain ⟨u,hu⟩ := hSurj a
  obtain ⟨v,hv⟩ := hSurj b
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  refine ⟨σ, liftBlockAutomorphism_graphAuto
    H block hBlocks hSurj q hq,?_⟩
  calc
    σ a = σ (block u) := by rw [hu]
    _ = block (q u) :=
      liftBlockAutomorphism_vertex H block hBlocks hSurj q hq u
    _ = b := by rw [hqu,hv]

/-- Precisely the blocks which intersect the distinguished copy of G. -/
noncomputable def occupiedBlocks {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) : Finset B :=
  (Finset.univ : Finset V).image (fun x => block (e x))

theorem mem_occupiedBlocks {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (b : B) :
    b ∈ occupiedBlocks e block ↔
      ∃ x : V, block (e x) = b := by
  classical
  simp [occupiedBlocks]

/-- If an EPPA embedding has all its base edges inside individual
blocks, the action on DISTINCT occupied blocks is ordered-pair
transitive. Only genuine two-point EPPA extensions are used. -/
theorem eppa_occupied_blocks_pair_transitive {V W B : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hEdgesInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y)) :
    ∀ a ∈ occupiedBlocks e block, ∀ b ∈ occupiedBlocks e block,
      a ≠ b →
      ∀ c ∈ occupiedBlocks e block, ∀ d ∈ occupiedBlocks e block,
      c ≠ d →
      ∃ σ : Equiv.Perm B,
        IsGraphAutomorphism (blockConnectionGraph H block) σ ∧
        σ a = c ∧ σ b = d := by
  classical
  intro a ha b hb hab c hc d hd hcd
  obtain ⟨x,hx⟩ := (mem_occupiedBlocks e block a).mp ha
  obtain ⟨y,hy⟩ := (mem_occupiedBlocks e block b).mp hb
  obtain ⟨z,hz⟩ := (mem_occupiedBlocks e block c).mp hc
  obtain ⟨w,hw⟩ := (mem_occupiedBlocks e block d).mp hd
  have hxy : x ≠ y := by
    intro h
    apply hab
    calc
      a = block (e x) := hx.symm
      _ = block (e y) := by rw [h]
      _ = b := hy
  have hzw : z ≠ w := by
    intro h
    apply hcd
    calc
      c = block (e z) := hz.symm
      _ = block (e w) := by rw [h]
      _ = d := hw
  have hNotXY : ¬ G.Adj x y := by
    intro h
    exact hab (hx.symm.trans ((hEdgesInside x y h).trans hy))
  have hNotZW : ¬ G.Adj z w := by
    intro h
    exact hcd (hz.symm.trans ((hEdgesInside z w h).trans hw))
  have hType : G.Adj x y ↔ G.Adj z w :=
    ⟨fun h => False.elim (hNotXY h),
     fun h => False.elim (hNotZW h)⟩
  obtain ⟨p,hpx,hpy,hPartial⟩ :=
    DoubleCover.partial_of_two_maps G x y z w hxy hzw hType
  obtain ⟨q,hq,hExtend⟩ :=
    heppa.2 ({x,y} : Finset V) p hPartial
  have hqx : q (e x) = e z := by
    calc
      q (e x) = e (p x) := hExtend x (by simp)
      _ = e z := by rw [hpx]
  have hqy : q (e y) = e w := by
    calc
      q (e y) = e (p y) := hExtend y (by simp)
      _ = e w := by rw [hpy]
  let σ := liftBlockAutomorphism H block hBlocks hSurj q hq
  refine ⟨σ, liftBlockAutomorphism_graphAuto
    H block hBlocks hSurj q hq, ?_, ?_⟩
  · calc
      σ a = σ (block (e x)) := congrArg σ hx.symm
      _ = block (q (e x)) :=
        liftBlockAutomorphism_vertex H block hBlocks hSurj q hq (e x)
      _ = block (e z) := by rw [hqx]
      _ = c := hz
  · calc
      σ b = σ (block (e y)) := congrArg σ hy.symm
      _ = block (q (e y)) :=
        liftBlockAutomorphism_vertex H block hBlocks hSurj q hq (e y)
      _ = block (e w) := by rw [hqy]
      _ = d := hw

/-- Combining the *actual* EPPA quotient action and the previous
majority-quotient theorem. Only the numerical majority hypothesis
and nonemptiness of the inter-block edge graph remain explicit. -/
theorem eppa_majority_occupied_blocks_complete {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype B] [Nonempty B]
    [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hEdgesInside : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y))
    (hMajority : Fintype.card B < 2 * (occupiedBlocks e block).card)
    (hNotEmpty : blockConnectionGraph H block ≠ ⊥) :
    blockConnectionGraph H block = ⊤ := by
  classical
  exact CliqueCovers.transitive_majority_pair_action_nonempty_top
    (blockConnectionGraph H block)
    (blockConnectionGraph_transitive H block hBlocks hSurj hTrans)
    (occupiedBlocks e block) hMajority
    (eppa_occupied_blocks_pair_transitive
      G H e heppa block hBlocks hSurj hEdgesInside)
    hNotEmpty

end EPPAIII.BlockSystems
