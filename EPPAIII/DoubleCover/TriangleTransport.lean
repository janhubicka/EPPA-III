import EPPAIII.BlockSystems.TransitivePartition

/-!
# Triangle counts are preserved by genuine graph automorphisms

We record ordered pairs of adjacent neighbours of a distinguished
vertex. Their cardinality counts each ordinary triangle twice,
which is harmless when comparing triangle numbers.

Using an actual automorphism q of the host, the map
(y,z) ↦ (q y,q z) bijects the two finite sets of such pairs.
This is a graph-level invariant, not an assumption of coherent
EPPA lifts or an algebraic identity about possible triangle scores.
-/

namespace EPPAIII.DoubleCover

/-- Ordered adjacent pairs in the neighbourhood of u. Each
unoriented triangle through u is represented twice. -/
noncomputable def orderedTrianglePairsAt {W : Type*}
    [Fintype W] (H : SimpleGraph W) (u : W) : Finset (W × W) := by
  classical
  exact (Finset.univ : Finset (W × W)).filter
    (fun yz => H.Adj u yz.1 ∧ H.Adj u yz.2 ∧ H.Adj yz.1 yz.2)

/-- Automorphisms preserve the number of ordered triangles
through each vertex, by an explicit bijection of triangle pairs. -/
theorem orderedTrianglePairsAt_card_graphAut {W : Type*}
    [Fintype W] (H : SimpleGraph W)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
    (u : W) :
    (orderedTrianglePairsAt H u).card =
      (orderedTrianglePairsAt H (q u)).card := by
  classical
  let f : W × W ≃ W × W := Equiv.prodCongr q q
  have hPattern (p : W × W) :
      p ∈ orderedTrianglePairsAt H u ↔
        f p ∈ orderedTrianglePairsAt H (q u) := by
    simp only [orderedTrianglePairsAt, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (H.Adj u p.1 ∧ H.Adj u p.2 ∧ H.Adj p.1 p.2) ↔
      (H.Adj (q u) (q p.1) ∧ H.Adj (q u) (q p.2) ∧
        H.Adj (q p.1) (q p.2))
    constructor
    · rintro ⟨h1,h2,h3⟩
      exact ⟨(hq u p.1).mp h1, (hq u p.2).mp h2,
        (hq p.1 p.2).mp h3⟩
    · rintro ⟨h1,h2,h3⟩
      exact ⟨(hq u p.1).mpr h1, (hq u p.2).mpr h2,
        (hq p.1 p.2).mpr h3⟩
  have hImage :
      (orderedTrianglePairsAt H u).image f =
        orderedTrianglePairsAt H (q u) := by
    ext p
    constructor
    · intro hp
      obtain ⟨a,ha,hfa⟩ := Finset.mem_image.mp hp
      rw [← hfa]
      exact (hPattern a).mp ha
    · intro hp
      refine Finset.mem_image.mpr ⟨f.symm p, ?_, by simp⟩
      apply (hPattern (f.symm p)).mpr
      simpa using hp
  calc
    (orderedTrianglePairsAt H u).card =
        ((orderedTrianglePairsAt H u).image f).card :=
      (Finset.card_image_of_injective
        (orderedTrianglePairsAt H u) f.injective).symm
    _ = (orderedTrianglePairsAt H (q u)).card :=
      congrArg Finset.card hImage

/-- Vertex transitivity makes the actual ordered triangle count
independent of the vertex. -/
theorem orderedTrianglePairsAt_card_transitive {W : Type*}
    [Fintype W] (H : SimpleGraph W)
    (hTrans : BlockSystems.IsVertexTransitive H)
    (u v : W) :
    (orderedTrianglePairsAt H u).card =
      (orderedTrianglePairsAt H v).card := by
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  simpa only [hqu] using
    orderedTrianglePairsAt_card_graphAut H q hq u

end EPPAIII.DoubleCover
