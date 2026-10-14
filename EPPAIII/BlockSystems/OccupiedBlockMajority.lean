import EPPAIII.BlockSystems.OccupiedBlockAction
import EPPAIII.BlockSystems.UnequalCliqueBaseBlocks

/-!
# Counting occupied blocks and excluding the empty quotient

In a vertex-transitive host with a uniform invariant partition,
the occupied block union has exactly m times the number of
occupied blocks. If any occupied block contains an outside vertex,
the distinguished induced copy occupies *strictly less* than
m vertices per occupied block on average. Since |H|=2|G|,
the occupied blocks form a strict majority.

If every invariant block induces a clique, a non-cluster H must
have an inter-block edge. These are the two remaining hypotheses
in the quotient-majority theorem for Lemma 3.12, Case 1.

The graph-theoretic steps are kept separate from proving that
the manuscript's unequal-clique hypotheses force a not-full block
and force each host block to induce a clique.
-/

namespace EPPAIII.BlockSystems

/-- The vertices in any block met by the selected copy. -/
noncomputable def occupiedHostVertices {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) : Finset W :=
  (Finset.univ : Finset W).filter
    (fun w => block w ∈ occupiedBlocks e block)

/-- Exactly |S|·m vertices of the host belong to the occupied
block union, provided every fibre of the partition has size m. -/
theorem occupiedHostVertices_card {V W B : Type*}
    [Fintype V] [Fintype W] [Fintype B] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m) :
    (occupiedHostVertices e block).card =
      (occupiedBlocks e block).card * m := by
  classical
  let S : Finset B := occupiedBlocks e block
  let U : Finset W := occupiedHostVertices e block
  have hFibre (b : B) :
      (U.filter (fun w => block w = b)).card =
        (if b ∈ S then m else 0) := by
    by_cases hb : b ∈ S
    · have hFilter :
          U.filter (fun w => block w = b) =
            (Finset.univ : Finset W).filter (fun w => block w = b) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hw
          refine ⟨?_,hw⟩
          change w ∈ occupiedHostVertices e block
          simp only [occupiedHostVertices, Finset.mem_filter,
            Finset.mem_univ, true_and]
          simpa [hw] using hb
      simpa [hb, hFilter] using hUniform b
    · have hFilter :
          U.filter (fun w => block w = b) = ∅ := by
        ext w
        constructor
        · intro hw
          have hwU : w ∈ U := (Finset.mem_filter.mp hw).1
          have hwB : block w = b := (Finset.mem_filter.mp hw).2
          have hwS : block w ∈ S := (Finset.mem_filter.mp hwU).2
          rw [hwB] at hwS
          exact False.elim (hb hwS)
        · intro hw
          simp at hw
      simp [hb, hFilter]
  have hSum :
      (∑ b : B, (U.filter (fun w => block w = b)).card) =
        U.card := by
    simpa using (Finset.sum_fiberwise U block (fun _ => (1 : ℕ)))
  calc
    (occupiedHostVertices e block).card = U.card := rfl
    _ = ∑ b : B, (U.filter (fun w => block w = b)).card :=
      hSum.symm
    _ = ∑ b : B, if b ∈ S then m else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      exact hFibre b
    _ = S.card * m := by simp
    _ = (occupiedBlocks e block).card * m := rfl

/-- If an occupied block contains a host vertex outside the copy
of G, it follows by finite counting that strictly more than half
the block indices are occupied. No regularity of cross edges is
assumed. -/
theorem occupied_blocks_strict_majority_of_nonfilled {V W B : Type*}
    [Fintype V] [Fintype W] [Fintype B] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (w : W) (hwOcc : block w ∈ occupiedBlocks e block)
    (hwOutside : w ∉ Set.range e) :
    Fintype.card B < 2 * (occupiedBlocks e block).card := by
  classical
  let S : Finset B := occupiedBlocks e block
  let U : Finset W := occupiedHostVertices e block
  let I : Finset W := (Finset.univ : Finset V).image e
  have hSelectedSubset : I ⊆ U := by
    intro z hz
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hz
    rw [← hx]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact (mem_occupiedBlocks e block (block (e x))).mpr ⟨x,rfl⟩
  have hwU : w ∈ U :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwOcc⟩
  have hwI : w ∉ I := by
    intro h
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    exact hwOutside ⟨x,hx⟩
  have hNotEqual : I.card ≠ U.card := by
    intro hCount
    have hEq : I = U :=
      Finset.eq_of_subset_of_card_le hSelectedSubset (by omega)
    have : w ∈ I := by rw [hEq]; exact hwU
    exact hwI this
  have hSmall : I.card < U.card := by
    have hLe := Finset.card_le_card hSelectedSubset
    omega
  have hImageCard : I.card = Fintype.card V := by
    simpa [I] using
      (Finset.card_image_of_injective
        (Finset.univ : Finset V) e.injective)
  have hOccupiedCard : U.card = S.card * m :=
    occupiedHostVertices_card e block m hUniform
  have hStrict : Fintype.card V < S.card * m := by
    calc
      Fintype.card V = I.card := hImageCard.symm
      _ < U.card := hSmall
      _ = S.card * m := hOccupiedCard
  have hTotal : Fintype.card B * m = 2 * Fintype.card V :=
    (uniform_partition_card_formula block m hUniform).trans hDouble
  have hProduct :
      Fintype.card B * m < (2 * S.card) * m := by
    calc
      Fintype.card B * m = 2 * Fintype.card V := hTotal
      _ < 2 * (S.card * m) := by omega
      _ = (2 * S.card) * m := by ring
  have hMajority : Fintype.card B < 2 * S.card := by
    by_contra h
    have hOpposite : 2 * S.card ≤ Fintype.card B := by omega
    have hMult : (2 * S.card) * m ≤ Fintype.card B * m :=
      Nat.mul_le_mul_right m hOpposite
    omega
  exact hMajority

/-- If every host block induces a clique and no two different
blocks are joined by an edge, the entire host is a disjoint
union of cliques. Hence non-cluster H forces an inter-block edge. -/
theorem blockConnectionGraph_nonempty_of_noncluster {W B : Type*}
    (H : SimpleGraph W) (block : W → B)
    (hBlockClique : ∀ u v : W, u ≠ v →
      block u = block v → H.Adj u v)
    (hNonCluster : ¬ IsClusterGraph H) :
    blockConnectionGraph H block ≠ ⊥ := by
  intro hEmpty
  have hEveryEdgeInternal (u v : W) (hAdj : H.Adj u v) :
      block u = block v := by
    by_contra hDifferent
    have hQ : (blockConnectionGraph H block).Adj (block u) (block v) :=
      ⟨hDifferent,u,v,rfl,rfl,hAdj⟩
    rw [hEmpty] at hQ
    exact hQ
  apply hNonCluster
  intro a b c hab hbc hac
  have hAC : block a = block c :=
    (hEveryEdgeInternal a b hab).trans (hEveryEdgeInternal b c hbc)
  exact hBlockClique a c hac hAC

/-- Full Case-1 majority-quotient conclusion under *actual* EPPA
actions, a non-cluster host whose invariant blocks induce cliques,
and existence of one occupied block containing an outside vertex.
Neither quotient transitivity, pair-transitivity nor the majority
inequality is postulated. -/
theorem eppa_noncluster_occupied_quotient_complete {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSomeInternalEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hBlockClique : ∀ u v : W, u ≠ v →
      block u = block v → H.Adj u v)
    (hNonCluster : ¬ IsClusterGraph H)
    (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (w : W) (hwOcc : block w ∈ occupiedBlocks e block)
    (hwOutside : w ∉ Set.range e) :
    blockConnectionGraph H block = ⊤ := by
  classical
  have hInternal : ∀ x y : V, G.Adj x y →
      block (e x) = block (e y) :=
    eppa_base_edges_internal_of_one
      G H e heppa block hBlocks hSomeInternalEdge
  have hMajority : Fintype.card B <
      2 * (occupiedBlocks e block).card :=
    occupied_blocks_strict_majority_of_nonfilled
      e block m hUniform hDouble w hwOcc hwOutside
  have hNonempty : blockConnectionGraph H block ≠ ⊥ :=
    blockConnectionGraph_nonempty_of_noncluster
      H block hBlockClique hNonCluster
  exact eppa_majority_occupied_blocks_complete
    G H e heppa block hBlocks hSurj hTrans hInternal
    hMajority hNonempty


/-- Selected base vertices lying inside a specified invariant block. -/
noncomputable def selectedInBlock {V W B : Type*}
    [Fintype V] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (b : B) : Finset V :=
  (Finset.univ : Finset V).filter (fun x => block (e x) = b)

/-- Each selected block fibre injects into the corresponding host
fibre, so its cardinality is bounded by the common block size. -/
theorem selectedInBlock_card_le_uniform {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (b : B) :
    (selectedInBlock e block b).card ≤ m := by
  classical
  have hSubset :
      (selectedInBlock e block b).image e ⊆
        (Finset.univ : Finset W).filter (fun w => block w = b) := by
    intro w hw
    obtain ⟨x,hx,hxw⟩ := Finset.mem_image.mp hw
    rw [← hxw]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  calc
    (selectedInBlock e block b).card =
        ((selectedInBlock e block b).image e).card :=
      (Finset.card_image_of_injective _ e.injective).symm
    _ ≤ ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card := Finset.card_le_card hSubset
    _ = m := hUniform b

/-- If the selected points fill strictly less than one host block,
there must be an outside vertex in that very block. -/
theorem exists_outside_in_partly_selected_block {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (b : B) (hSmall : (selectedInBlock e block b).card < m) :
    ∃ w : W, block w = b ∧ w ∉ Set.range e := by
  classical
  by_contra hNo
  have hFull :
      ((Finset.univ : Finset W).filter (fun w => block w = b)) ⊆
        (selectedInBlock e block b).image e := by
    intro w hw
    have hwB : block w = b := (Finset.mem_filter.mp hw).2
    by_cases hwRange : w ∈ Set.range e
    · obtain ⟨x,hx⟩ := hwRange
      refine Finset.mem_image.mpr ⟨x,?_,hx⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,by simpa [hx] using hwB⟩
    · exact False.elim (hNo ⟨w,hwB,hwRange⟩)
  have hLe : m ≤ (selectedInBlock e block b).card := by
    calc
      m = ((Finset.univ : Finset W).filter
          (fun w => block w = b)).card := (hUniform b).symm
      _ ≤ ((selectedInBlock e block b).image e).card :=
        Finset.card_le_card hFull
      _ = (selectedInBlock e block b).card :=
        Finset.card_image_of_injective _ e.injective
  omega

/-- Unequal selected cardinalities in two *occupied* invariant
blocks force at least one of those blocks to contain a vertex of
H outside the selected G. -/
theorem unequal_occupied_sizes_give_outside {V W B : Type*}
    [Fintype V] [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = m)
    (b c : B)
    (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    ∃ w : W, block w ∈ occupiedBlocks e block ∧
      w ∉ Set.range e := by
  have hB := selectedInBlock_card_le_uniform e block m hUniform b
  have hC := selectedInBlock_card_le_uniform e block m hUniform c
  have hSmall : (selectedInBlock e block b).card < m ∨
      (selectedInBlock e block c).card < m := by omega
  rcases hSmall with hs | hs
  · obtain ⟨w,hwB,hwOut⟩ :=
      exists_outside_in_partly_selected_block
        e block m hUniform b hs
    exact ⟨w,by simpa [hwB] using hb,hwOut⟩
  · obtain ⟨w,hwC,hwOut⟩ :=
      exists_outside_in_partly_selected_block
        e block m hUniform c hs
    exact ⟨w,by simpa [hwC] using hc,hwOut⟩

/-- The Case-1 quotient is complete once two occupied blocks
contain different numbers of selected vertices. All other
hypotheses are structural properties of the actual invariant
partition and EPPA host, not of a postulated quotient action. -/
theorem eppa_unequal_occupied_quotient_complete {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W]
    [Fintype B] [Nonempty B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSomeInternalEdge : ∃ x y : V,
      G.Adj x y ∧ block (e x) = block (e y))
    (hBlockClique : ∀ u v : W, u ≠ v →
      block u = block v → H.Adj u v)
    (hNonCluster : ¬ IsClusterGraph H)
    (m : ℕ)
    (hUniform : ∀ b : B,
      ((Finset.univ : Finset W).filter (fun w => block w = b)).card = m)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (b c : B)
    (hb : b ∈ occupiedBlocks e block)
    (hc : c ∈ occupiedBlocks e block)
    (hDifferent :
      (selectedInBlock e block b).card ≠
        (selectedInBlock e block c).card) :
    blockConnectionGraph H block = ⊤ := by
  obtain ⟨w,hwOcc,hwOut⟩ :=
    unequal_occupied_sizes_give_outside
      e block m hUniform b c hb hc hDifferent
  exact eppa_noncluster_occupied_quotient_complete
    G H e heppa block hBlocks hSurj hTrans
    hSomeInternalEdge hBlockClique hNonCluster
    m hUniform hDouble w hwOcc hwOut

end EPPAIII.BlockSystems
