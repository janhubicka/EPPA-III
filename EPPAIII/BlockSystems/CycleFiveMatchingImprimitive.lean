import EPPAIII.BlockSystems.CycleFivePetersenPrimitivity

/-!
# Transport the Petersen block obstruction to actual C5 EPPA hosts

The preceding finite certificate proves that the canonical
Petersen matching model admits no nontrivial invariant block
partition under a transitive automorphism action. Here we transport
arbitrary host block maps along the *actual* graph equivalence
provided by the singleton-neighbourhood classification.

Consequently a ten-vertex transitive, imprimitive EPPA witness of C5
with one outside singleton profile has the prism matching pattern,
not the primitive Petersen pattern. The original manuscript is not
modified. No coherent choice of EPPA lifts is assumed.
-/

namespace EPPAIII.BlockSystems

/-- A genuine invariant block map transports along any equivalence
of host vertex types. The action of host automorphisms is conjugated
by that equivalence, not assumed in compatible coordinates. -/
theorem invariantBlockMap_comap_equiv
    {X W B : Type*}
    (H : SimpleGraph W) (phi : X ≃ W)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block) :
    InvariantBlockMap (H.comap phi) (fun x => block (phi x)) := by
  intro q hq x y
  let qW : Equiv.Perm W := (phi.symm.trans q).trans phi
  have hMove (z : X) : qW (phi z) = phi (q z) := by
    simp [qW, Equiv.trans_apply]
  have hW : IsGraphAutomorphism H qW := by
    intro u v
    have h := hq (phi.symm u) (phi.symm v)
    change H.Adj (phi (phi.symm u)) (phi (phi.symm v)) ↔
      H.Adj (phi (q (phi.symm u))) (phi (q (phi.symm v))) at h
    simpa only [phi.apply_symm_apply, ← hMove] using h
  have h := hBlocks qW hW (phi x) (phi y)
  simpa only [hMove x, hMove y] using h

/-- Two distinct points in one block guarantee that the actual
finite fibre has cardinality at least two. -/
theorem block_fibre_ge_two_of_equal_pair
    {X B : Type*} [Fintype X] [DecidableEq X] [DecidableEq B]
    (block : X → B) (x y : X) (hxy : x ≠ y)
    (hBlock : block x = block y) :
    2 ≤ ((Finset.univ : Finset X).filter
      (fun z => block z = block x)).card := by
  classical
  have hSub :
      ({x,y} : Finset X) ⊆
        ((Finset.univ : Finset X).filter
          (fun z => block z = block x)) := by
    intro z hz
    have hzCases : z = x ∨ z = y := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
    rcases hzCases with rfl | rfl
    · simp
    · simp [hBlock.symm]
  have hCount : ({x,y} : Finset X).card = 2 := by
    simpa using Finset.card_pair hxy
  have hLe := Finset.card_le_card hSub
  omega

/-- In the actual host, a nontrivial invariant partition rules out
the Petersen matching model and leaves the prism model. -/
theorem cycleFive_eppa_singleton_imprimitive_host_is_prism
    {W B : Type*} [Fintype W] [Fintype B] [DecidableEq B]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (block : W → B)
    (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hManyBlocks : 2 ≤ Fintype.card B)
    (u v : W) (huv : u ≠ v)
    (hSame : block u = block v)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ phi : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, phi (false,x) = e x) ∧
      H.comap phi = cycleFiveMatchingGraph false := by
  classical
  obtain ⟨phi,topComplement,hBottom,hGraph⟩ :=
    cycleFive_eppa_singleton_host_two_matching_graphs
      H e heppa hTrans hTen w hw hOne
  cases topComplement with
  | false =>
      exact ⟨phi,hBottom,hGraph⟩
  | true =>
      let b : Bool × Fin 5 → B := fun x => block (phi x)
      have hInv :
          InvariantBlockMap (cycleFiveMatchingGraph true) b := by
        rw [← hGraph]
        exact invariantBlockMap_comap_equiv H phi block hBlocks
      have hTransP :
          CliqueCovers.HasTransitiveGraphAutomorphisms
            (cycleFiveMatchingGraph true) := by
        rw [← hGraph]
        exact CliqueCovers.transitive_comap_equiv H phi hTrans
      have hSurjP : Function.Surjective b := by
        intro z
        obtain ⟨t,ht⟩ := hSurj z
        refine ⟨phi.symm t,?_⟩
        simpa [b] using ht
      let x : Bool × Fin 5 := phi.symm u
      let y : Bool × Fin 5 := phi.symm v
      have hxy : x ≠ y := phi.symm.injective.ne huv
      have hBxy : b x = b y := by
        simpa [b,x,y] using hSame
      have hLarge :
          2 ≤ ((Finset.univ : Finset (Bool × Fin 5)).filter
            (fun t => b t = b x)).card :=
        block_fibre_ge_two_of_equal_pair b x y hxy hBxy
      exact False.elim
        (petersen_no_nontrivial_invariant_partition
          b hInv hSurjP hTransP hManyBlocks ⟨b x,hLarge⟩)

end EPPAIII.BlockSystems
