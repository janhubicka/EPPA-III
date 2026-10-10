import EPPAIII.BlockSystems.Size

/-!
# Deriving uniform block sizes from actual host vertex-transitivity

A nontrivial imprimitivity system is an Aut(H)-invariant surjective
map from host vertices to block labels. The action of Aut(H) is
transitive on vertices; hence it is transitive on blocks and all
fibres have the same cardinality.

We prove both facts and the total-size identity in Lean, then remove
those auxiliary hypotheses from the earlier conditional Claim 3.4
counting theorem.
-/

namespace EPPAIII.BlockSystems

/-- Vertex-transitivity in the same permutation interface as
the rest of EPPA--III. -/
def IsVertexTransitive {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ u v : W, ∃ q : Equiv.Perm W,
    IsGraphAutomorphism H q ∧ q u = v

/-- Transitivity of the host and invariance of the partition imply
that any two blocks have equally many vertices. -/
theorem transitive_block_fibres_equal {W B : Type*}
    [Fintype W] [DecidableEq B]
    (H : SimpleGraph W) (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (b c : B) :
    ((Finset.univ : Finset W).filter (fun w => block w = b)).card =
      ((Finset.univ : Finset W).filter (fun w => block w = c)).card := by
  classical
  obtain ⟨u, hu⟩ := hSurj b
  obtain ⟨v, hv⟩ := hSurj c
  obtain ⟨q, hq, hqu⟩ := hTrans u v
  have hIff (w : W) : block w = b ↔ block (q w) = c := by
    calc
      block w = b ↔ block w = block u := by simp [hu]
      _ ↔ block (q w) = block (q u) := hBlocks q hq w u
      _ ↔ block (q w) = c := by simp [hqu, hv]
  let sb : Finset W :=
    (Finset.univ : Finset W).filter (fun w => block w = b)
  let sc : Finset W :=
    (Finset.univ : Finset W).filter (fun w => block w = c)
  have hImage : sb.image q = sc := by
    ext w
    simp only [sb, sc, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨z, hz, hzw⟩
      have hh : block (q z) = c := (hIff z).mp hz
      simpa [hzw] using hh
    · intro hw
      refine ⟨q.symm w, ?_, by simp⟩
      apply (hIff (q.symm w)).mpr
      simpa using hw
  calc
    sb.card = (sb.image q).card :=
      (Finset.card_image_of_injective sb q.injective).symm
    _ = sc.card := congrArg Finset.card hImage

/-- A uniform partition always has number-of-blocks times
block-size vertices. No transitivity is needed once the
sizes have been proved equal. -/
theorem uniform_partition_card_formula {W B : Type*}
    [Fintype W] [Fintype B] [DecidableEq B]
    (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m) :
    Fintype.card B * m = Fintype.card W := by
  classical
  have hSum :
      (∑ b : B,
        ((Finset.univ : Finset W).filter (fun w => block w = b)).card) =
        Fintype.card W := by
    simpa using
      (Finset.sum_fiberwise
        (Finset.univ : Finset W) block (fun _ => (1 : ℕ)))
  calc
    Fintype.card B * m = ∑ _b : B, m := by simp
    _ = ∑ b : B,
          ((Finset.univ : Finset W).filter (fun w => block w = b)).card := by
      apply Finset.sum_congr rfl
      intro b _
      exact (hUniform b).symm
    _ = Fintype.card W := hSum

/-- A version of Claim 3.4 using genuine transitivity and a
nontrivial invariant partition, without postulating equal block
sizes or a block-count formula. The only nontrivial-size assumption
says that at least one block has at least two vertices. -/
theorem transitive_eppa_blocks_are_pairs {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [Fintype B]
    [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B)
    (hTrans : IsVertexTransitive H)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hNonHomogeneous : ¬ DoubleCover.IsHomogeneousGraph G)
    (hNonCluster : ¬ IsClusterGraph G)
    (hNonCoCluster : ¬ IsCoClusterGraph G)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    Function.Injective (fun x : V => block (e x)) ∧
      Fintype.card B = Fintype.card V ∧
      (∀ b : B,
        ((Finset.univ : Finset W).filter (fun w => block w = b)).card = 2) := by
  classical
  obtain ⟨b₀, hb₀⟩ := hNontrivial
  let m : ℕ :=
    ((Finset.univ : Finset W).filter (fun w => block w = b₀)).card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal H block hTrans hBlocks hSurj b b₀
  have hOrder : Fintype.card B * m = 2 * Fintype.card V :=
    (uniform_partition_card_formula block m hUniform).trans hHostSize
  obtain ⟨hInject,hCount,hTwo⟩ := invariant_blocks_are_pairs
    G H e heppa block hBlocks
    hNonHomogeneous hNonCluster hNonCoCluster
    m hManyBlocks hb₀ hUniform hOrder
  refine ⟨hInject,hCount,?_⟩
  intro b
  rw [hUniform b]
  exact hTwo

end EPPAIII.BlockSystems
