import EPPAIII.BlockSystems.TransversalLiftBlocks
import EPPAIII.BlockSystems.UnequalCliqueBaseBlocks

/-!
# Genuine EPPA lifts from independent occupied-block transversals

If the invariant block relation on the selected graph agrees with
equality-or-adjacency, any two selected vertices in different host
blocks lie in an independent transversal meeting every occupied
block. Swapping those two representatives preserves the induced
empty graph on that transversal and is therefore a partial
automorphism of G.

By genuine EPPA the swap extends to H. If U is the unique block
disjoint from G, the already verified full-transversal lemma forces
the induced block permutation to fix U. This constructs the
desired fixed-U automorphism without coherent choices of lifts.

The same-block and global transitivity consequences are left for
a short separate composition using two different-block lifts.
-/

namespace EPPAIII.BlockSystems

/-- Find an independent transversal of all selected occupied blocks
containing two prescribed selected vertices in different blocks. -/
theorem exists_independent_transversal_with_two {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (e : V ↪ W) (block : W → B)
    (hSame : ∀ a b : V,
      block (e a) = block (e b) ↔ a = b ∨ G.Adj a b)
    (x y : V) (hDifferent : block (e x) ≠ block (e y)) :
    ∃ D : Finset V,
      x ∈ D ∧ y ∈ D ∧
      (∀ b ∈ occupiedBlocks e block,
        ∃ z ∈ D, block (e z) = b) ∧
      G.IsIndepSet (D : Set V) := by
  classical
  let S : Finset B := occupiedBlocks e block
  have hxS : block (e x) ∈ S :=
    (mem_occupiedBlocks e block (block (e x))).mpr ⟨x,rfl⟩
  have hyS : block (e y) ∈ S :=
    (mem_occupiedBlocks e block (block (e y))).mpr ⟨y,rfl⟩
  let rep : {b : B // b ∈ S} → V := fun z =>
    if hzX : z.1 = block (e x) then x
    else if hzY : z.1 = block (e y) then y
    else Classical.choose ((mem_occupiedBlocks e block z.1).mp z.2)
  have hRep (z : {b : B // b ∈ S}) : block (e (rep z)) = z.1 := by
    dsimp [rep]
    split_ifs with hx hy
    · exact hx.symm
    · exact hy.symm
    · exact Classical.choose_spec
        ((mem_occupiedBlocks e block z.1).mp z.2)
  let D : Finset V := (Finset.univ : Finset {b : B // b ∈ S}).image rep
  have hxMem : x ∈ D := by
    let ix : {b : B // b ∈ S} := ⟨block (e x),hxS⟩
    have hRepX : rep ix = x := by
      simp [rep,ix]
    exact Finset.mem_image.mpr ⟨ix, Finset.mem_univ _, hRepX⟩
  have hyMem : y ∈ D := by
    let iy : {b : B // b ∈ S} := ⟨block (e y),hyS⟩
    have hRepY : rep iy = y := by
      simp [rep,iy,hDifferent.symm]
    exact Finset.mem_image.mpr ⟨iy, Finset.mem_univ _,hRepY⟩
  have hHits : ∀ b ∈ S, ∃ z ∈ D, block (e z) = b := by
    intro b hb
    let ib : {z : B // z ∈ S} := ⟨b,hb⟩
    refine ⟨rep ib, ?_, hRep ib⟩
    exact Finset.mem_image.mpr ⟨ib,Finset.mem_univ _,rfl⟩
  have hDistinct (u v : V) (hu : u ∈ D) (hv : v ∈ D)
      (hBlocksEq : block (e u) = block (e v)) : u = v := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hv
    have hIndex : i.1 = j.1 := by
      calc
        i.1 = block (e (rep i)) := (hRep i).symm
        _ = block (e u) := by rw [hi]
        _ = block (e v) := hBlocksEq
        _ = block (e (rep j)) := by rw [hj]
        _ = j.1 := hRep j
    have hij : i = j := Subtype.ext hIndex
    calc
      u = rep i := hi.symm
      _ = rep j := congrArg rep hij
      _ = v := hj
  have hIndependent : G.IsIndepSet (D : Set V) := by
    intro u hu v hv huv hAdj
    have hBlockSame := (hSame u v).mpr (Or.inr hAdj)
    exact huv (hDistinct u v hu hv hBlockSame)
  exact ⟨D,hxMem,hyMem,by simpa [S] using hHits,hIndependent⟩

/-- Swapping two points of an independent finite set is a partial
automorphism on that set. No global automorphism is implied. -/
theorem swap_partial_on_independent_finset {V : Type*}
    [DecidableEq V]
    (G : SimpleGraph V) (D : Finset V)
    (hIndependent : G.IsIndepSet (D : Set V))
    (x y : V) (hx : x ∈ D) (hy : y ∈ D) :
    IsPartialGraphAutomorphism G D (Equiv.swap x y) := by
  have hMap (u : V) (hu : u ∈ D) :
      (Equiv.swap x y) u ∈ D := by
    by_cases hux : u = x
    · subst u
      simpa using hy
    · by_cases huy : u = y
      · subst u
        simpa using hx
      · have hFixed : (Equiv.swap x y) u = u :=
          Equiv.swap_apply_of_ne_of_ne hux huy
        simpa [hFixed] using hu
  intro u v hu hv
  constructor
  · intro hAdj
    exact False.elim
      (hIndependent hu hv (G.ne_of_adj hAdj) hAdj)
  · intro hAdj
    exact False.elim
      (hIndependent (hMap u hu) (hMap v hv)
        (G.ne_of_adj hAdj) hAdj)

/-- Actual EPPA lifts map arbitrary selected vertices lying in
different host blocks to one another while fixing the unique
unoccupied block. -/
theorem eppa_fixed_unoccupied_lift_between_blocks {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hSame : ∀ a b : V,
      block (e a) = block (e b) ↔ a = b ∨ G.Adj a b)
    (U : B) (hU : U ∉ occupiedBlocks e block)
    (hOnly : ∀ b : B, b ∉ occupiedBlocks e block → b = U)
    (x y : V) (hDifferent : block (e x) ≠ block (e y)) :
    ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q),
      q (e x) = e y ∧
      (∀ z : W, block z = U ↔ block (q z) = U) := by
  classical
  obtain ⟨D,hx,hy,hHits,hIndep⟩ :=
    exists_independent_transversal_with_two G e block hSame
      x y hDifferent
  have hp : IsPartialGraphAutomorphism G D (Equiv.swap x y) :=
    swap_partial_on_independent_finset G D hIndep x y hx hy
  obtain ⟨q,hq,hFixU,hExt⟩ :=
    eppa_transversal_lift_fixes_unique_unoccupied
      G H e heppa block hBlocks hSurj
      U hU hOnly D hHits (Equiv.swap x y) hp
  have hMap : q (e x) = e y := by
    simpa using hExt x hx
  let σ : Equiv.Perm B :=
    liftBlockAutomorphism H block hBlocks hSurj q hq
  have hPreserve (z : W) : block z = U ↔ block (q z) = U := by
    constructor
    · intro hz
      calc
        block (q z) = σ (block z) :=
          (liftBlockAutomorphism_vertex H block hBlocks hSurj q hq z).symm
        _ = σ U := by rw [hz]
        _ = U := hFixU
    · intro hz
      apply σ.injective
      calc
        σ (block z) = block (q z) :=
          liftBlockAutomorphism_vertex H block hBlocks hSurj q hq z
        _ = U := hz
        _ = σ U := hFixU.symm
  exact ⟨q,hq,hMap,hPreserve⟩

end EPPAIII.BlockSystems
