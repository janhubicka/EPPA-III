import EPPAIII.DoubleCover.TwoPointAction

/-!
# The first block-system step in Lemma 3.3 (Claim 3.4)

The manuscript begins with a nontrivial invariant imprimitivity
partition of H. Represent such a partition by its map of vertices to
block labels. Its one crucial invariant is the equivalence relation:
  block u = block v ↔ block (q u) = block (q v)
for each graph automorphism q.

The two-point EPPA property then implies that the block relation has
a uniform truth value on ordered base edges, and another uniform truth
value on ordered distinct base nonedges. This supplies the exact
formal input for the transversality argument in Claim 3.4.

No size or structure of blocks is assumed in these orbit lemmas.
-/

namespace EPPAIII.BlockSystems

/-- An Aut(H)-invariant partition, recorded as its block-label map.
The map need not be injective; equality of block labels means
membership in the same imprimitivity block. -/
def InvariantBlockMap {W B : Type*}
    (H : SimpleGraph W) (block : W → B) : Prop :=
  ∀ (q : Equiv.Perm W), IsGraphAutomorphism H q →
    ∀ w₁ w₂ : W,
      block w₁ = block w₂ ↔ block (q w₁) = block (q w₂)

/-- An EPPA extension of a two-point isomorphism preserves whether
the two selected vertices lie in the same imprimitivity block.
This works with any block system and any induced embedding. -/
theorem eppa_block_relation_two_point {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hadj : G.Adj x y ↔ G.Adj u v) :
    (block (e x) = block (e y) ↔
       block (e u) = block (e v)) := by
  classical
  obtain ⟨p, hpX, hpY, hpPartial⟩ :=
    DoubleCover.partial_of_two_maps G x y u v hxy huv hadj
  obtain ⟨q, hq, hRestrict⟩ :=
    heppa.2 ({x,y} : Finset V) p hpPartial
  have hX : q (e x) = e u := by
    simpa [hpX] using hRestrict x (by simp)
  have hY : q (e y) = e v := by
    simpa [hpY] using hRestrict y (by simp)
  simpa [hX, hY] using hBlocks q hq (e x) (e y)

/-- Every two base edges have the same within-block/cross-block
status, even though their EPPA extensions need not be coherent. -/
theorem eppa_edges_uniform_blocks {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (x y u v : V) (hxy : G.Adj x y) (huv : G.Adj u v) :
    (block (e x) = block (e y) ↔
       block (e u) = block (e v)) := by
  apply eppa_block_relation_two_point G H e heppa block hBlocks
    x y u v (G.ne_of_adj hxy) (G.ne_of_adj huv)
  exact ⟨fun _ => huv, fun _ => hxy⟩

/-- Every two distinct base nonedges have the same block status. -/
theorem eppa_nonedges_uniform_blocks {V W B : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (x y u v : V)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hnxy : ¬ G.Adj x y) (hnuv : ¬ G.Adj u v) :
    (block (e x) = block (e y) ↔
       block (e u) = block (e v)) := by
  apply eppa_block_relation_two_point G H e heppa block hBlocks
    x y u v hxy huv
  exact ⟨fun h => False.elim (hnxy h),
    fun h => False.elim (hnuv h)⟩

/-- Elementary cardinal arithmetic for a regular block partition
of a double-sized host. If the distinguished n vertices meet
distinct blocks and every block has size m≥2, the host has
exactly n blocks and each has size two. -/
theorem transversal_double_count
    (numberOfBlocks blockSize n : ℕ)
    (hBlocks : 0 < numberOfBlocks)
    (hSize : 2 ≤ blockSize)
    (hInject : n ≤ numberOfBlocks)
    (hOrder : numberOfBlocks * blockSize = 2 * n) :
    numberOfBlocks = n ∧ blockSize = 2 := by
  have hlower : numberOfBlocks * 2 ≤ numberOfBlocks * blockSize :=
    Nat.mul_le_mul_left numberOfBlocks hSize
  have hupper : numberOfBlocks ≤ n := by omega
  have heq : numberOfBlocks = n := by omega
  constructor
  · exact heq
  · nlinarith

end EPPAIII.BlockSystems
