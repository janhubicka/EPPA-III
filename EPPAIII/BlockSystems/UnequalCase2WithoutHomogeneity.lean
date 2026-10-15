import EPPAIII.BlockSystems.UnequalCase2Triangle

/-!
# Unequal clique sizes automatically imply base non-homogeneity

For a finite homogeneous graph, one-point partial automorphisms
extend; hence its automorphism group is vertex-transitive. An
automorphism preserves the number of neighbours. Thus unequal
degrees immediately contradict homogeneity.

This removes the extraneous non-homogeneity hypothesis of the base
from the unequal-clique Case-2 triangle obstruction, while retaining
the actual invariant-partition and EPPA hypotheses. No homogeneous
graph classification is used.
-/

namespace EPPAIII.BlockSystems

theorem graph_automorphism_preserves_base_neighbour_card
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (q : Equiv.Perm V)
    (hq : IsGraphAutomorphism G q) (x : V) :
    (DoubleCover.clusterBaseNeighbours G x).card =
      (DoubleCover.clusterBaseNeighbours G (q x)).card := by
  classical
  have hImage :
      (DoubleCover.clusterBaseNeighbours G x).image q =
        DoubleCover.clusterBaseNeighbours G (q x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨v,hv,hqv⟩ := Finset.mem_image.mp hz
      have hXV : G.Adj x v := by
        simpa [DoubleCover.clusterBaseNeighbours] using hv
      have hQ : G.Adj (q x) (q v) := (hq x v).mp hXV
      have hZ : G.Adj (q x) z := by
        simpa [hqv] using hQ
      simpa [DoubleCover.clusterBaseNeighbours] using hZ
    · intro hz
      let v : V := q.symm z
      have hZ : G.Adj (q x) z := by
        simpa [DoubleCover.clusterBaseNeighbours] using hz
      have hXV : G.Adj x v := (hq x v).mpr (by
        simpa [v] using hZ)
      exact Finset.mem_image.mpr
        ⟨v, by simpa [DoubleCover.clusterBaseNeighbours] using hXV,
          by simp [v]⟩
  calc
    (DoubleCover.clusterBaseNeighbours G x).card =
        ((DoubleCover.clusterBaseNeighbours G x).image q).card :=
      (Finset.card_image_of_injective
        (DoubleCover.clusterBaseNeighbours G x) q.injective).symm
    _ = (DoubleCover.clusterBaseNeighbours G (q x)).card :=
      congrArg Finset.card hImage

/-- Extend the one-point partial permutation to obtain transitivity
directly from the definition of homogeneous graph. -/
theorem homogeneous_graph_vertex_transitive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hHomogeneous : DoubleCover.IsHomogeneousGraph G) :
    IsVertexTransitive G := by
  intro x y
  let p : Equiv.Perm V := Equiv.swap x y
  have hPartial :
      IsPartialGraphAutomorphism G ({x} : Finset V) p := by
    intro u v hu hv
    have huX : u = x := by simpa using hu
    have hvX : v = x := by simpa using hv
    subst u
    subst v
    simp
  obtain ⟨q,hq,hExt⟩ := hHomogeneous {x} p hPartial
  refine ⟨q,hq,?_⟩
  simpa [p] using hExt x (by simp)

/-- A finite graph with two vertices of unequal degrees cannot
be homogeneous. This is a one-point orbit obstruction. -/
theorem nonhomogeneous_of_unequal_base_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card) :
    ¬ DoubleCover.IsHomogeneousGraph G := by
  intro hHomogeneous
  obtain ⟨q,hq,hXY⟩ :=
    homogeneous_graph_vertex_transitive G hHomogeneous x y
  have hCount :=
    graph_automorphism_preserves_base_neighbour_card G q hq x
  rw [hXY] at hCount
  exact hDifferent hCount

/-- Case 2 with unequal clique sizes needs no separate hypothesis
that the base is non-homogeneous: unequal degrees already ensure it. -/
theorem transitive_eppa_case2_unequal_three_components
    {V W B : Type*}
    [Fintype V] [DecidableEq V]
    [Fintype W] [Fintype B] [DecidableEq B]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hSurj : Function.Surjective block)
    (hTrans : IsVertexTransitive H)
    (hCluster : IsClusterGraph G)
    (hCoP3 : HasInducedCoP3 G)
    (hCross : ∃ x y : V,
      G.Adj x y ∧ block (e x) ≠ block (e y))
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b₀ : B, 2 ≤
      ((Finset.univ : Finset W).filter
        (fun w => block w = b₀)).card)
    (hHostSize : Fintype.card W = 2 * Fintype.card V)
    (x y : V)
    (hDifferent :
      (DoubleCover.clusterBaseNeighbours G x).card ≠
        (DoubleCover.clusterBaseNeighbours G y).card)
    (hThird :
      (DoubleCover.clusterBaseNeighbours G x).card +
        (DoubleCover.clusterBaseNeighbours G y).card + 2 <
          Fintype.card V) : False := by
  have hNonHomogeneous :=
    nonhomogeneous_of_unequal_base_degrees G x y hDifferent
  exact transitive_eppa_case2_unequal_three_components_impossible
    G H e heppa block hBlocks hSurj hTrans
    hNonHomogeneous hCluster hCoP3 hCross hManyBlocks
    hNontrivial hHostSize x y hDifferent hThird

end EPPAIII.BlockSystems
