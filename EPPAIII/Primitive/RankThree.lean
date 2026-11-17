import EPPAIII.BlockSystems.SmallHostRankThreeStatement
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Graph-theoretic inputs to the primitive rank-three classification

The rank-three conclusion for a small EPPA witness is proved in
`SmallHostRankThreeStatement`. This file derives the graph-theoretic
properties used to apply the separate external classification.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- Ordered pair transitivity fixes the root when both pairs start there. -/
theorem rankThree_point_stabilizer {W : Type*} (H : SimpleGraph W)
    (hRank : HasRankThreeAutAction H)
    (root u v : W) (hu : root ≠ u) (hv : root ≠ v)
    (hStatus : H.Adj root u ↔ H.Adj root v) :
    ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q root = root ∧ q u = v :=
  hRank.2.2.2 root u root v hu hv hStatus

/-- Restrict a root stabilizer to either off-diagonal root status. This
uses the induced adjacency on the subtype, without any assertion about
the full automorphism group of the subconstituent. -/
theorem rankThree_pointwise_transitive {W : Type*} (H : SimpleGraph W)
    (hRank : HasRankThreeAutAction H) (root : W) (adjacent : Prop) :
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (H.induce {x | root ≠ x ∧ (H.Adj root x ↔ adjacent)}) := by
  intro u v
  obtain ⟨q, hq, hRoot, hUV⟩ :=
    rankThree_point_stabilizer H hRank root u v u.property.1 v.property.1
      (u.property.2.trans v.property.2.symm)
  have hPreserves (x : W) :
      (root ≠ x ∧ (H.Adj root x ↔ adjacent)) ↔
        (root ≠ q x ∧ (H.Adj root (q x) ↔ adjacent)) := by
    have hNe : root ≠ x ↔ root ≠ q x := by
      calc
        root ≠ x ↔ q root ≠ q x :=
          ⟨fun h heq => h (q.injective heq), fun h heq => h (congrArg q heq)⟩
        _ ↔ root ≠ q x := by rw [hRoot]
    have hAdj := hq root x
    rw [hRoot] at hAdj
    exact and_congr hNe (iff_congr hAdj Iff.rfl)
  refine ⟨q.subtypeEquiv hPreserves, ?_, Subtype.ext hUV⟩
  intro x y
  exact hq x y

private theorem card_commonNeighbors_of_automorphism {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) (x y : W) :
    Fintype.card (H.commonNeighbors x y) =
      Fintype.card (H.commonNeighbors (q x) (q y)) :=
  Fintype.card_congr (q.subtypeEquiv (fun z => and_congr (hq x z) (hq y z)))

/-- A rank-three graph is strongly regular. The degree and both common
neighbor counts are constant on the corresponding full automorphism
orbits. Primitivity is unnecessary for this conclusion. -/
theorem rankThree_isSRG {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hRank : HasRankThreeAutAction H) :
    ∃ k l m, H.IsSRGWith (Fintype.card W) k l m := by
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hNotCD⟩, hTrans, hPairs⟩ := hRank
  refine ⟨H.degree a, Fintype.card (H.commonNeighbors a b),
    Fintype.card (H.commonNeighbors c d), rfl, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨q, hq, hqv⟩ := hTrans v a
    exact (EPPAIII.CliqueCovers.graphAuto_preserves_degree H q hq v).symm.trans
      (congrArg (fun x : W => H.degree x) hqv)
  · intro u v huv
    obtain ⟨q, hq, hqu, hqv⟩ :=
      hPairs u v a b (H.ne_of_adj huv) (H.ne_of_adj hab)
        ⟨fun _ => hab, fun _ => huv⟩
    simpa only [hqu, hqv] using card_commonNeighbors_of_automorphism H q hq u v
  · intro u v huv hNotUV
    obtain ⟨q, hq, hqu, hqv⟩ := hPairs u v c d huv hcd
      ⟨fun h => (hNotUV h).elim, fun h => (hNotCD h).elim⟩
    simpa only [hqu, hqv] using card_commonNeighbors_of_automorphism H q hq u v

/-- In a primitive rank-three action, the graph and its complement are
connected. The two non-diagonal orbits give the edge required on each
side of the elementary invariant-reachability argument. -/
theorem primitive_rankThree_connected {W : Type*} (H : SimpleGraph W)
    (hPrimitive : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H) :
    H.Connected ∧ Hᶜ.Connected := by
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hNotCD⟩, _⟩ := hRank
  constructor
  · exact { preconnected := primitive_invariant_nonempty_graph_preconnected
              H H hPrimitive (fun _ hq => hq) a b hab
            nonempty := ⟨a⟩ }
  · have hInvariant : ∀ q : Equiv.Perm W,
        IsGraphAutomorphism H q → IsGraphAutomorphism Hᶜ q := by
      intro q hq u v
      have hNe : u ≠ v ↔ q u ≠ q v :=
        ⟨fun h heq => h (q.injective heq), fun h heq => h (congrArg q heq)⟩
      exact and_congr hNe (not_congr (hq u v))
    exact { preconnected := primitive_invariant_nonempty_graph_preconnected
              H Hᶜ hPrimitive hInvariant c d ⟨hcd, hNotCD⟩
            nonempty := ⟨a⟩ }

end EPPAIII.Primitive
