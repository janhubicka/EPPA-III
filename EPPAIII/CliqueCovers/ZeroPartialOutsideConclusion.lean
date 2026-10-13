import EPPAIII.CliqueCovers.ZeroPartialNoncluster
import EPPAIII.CliqueCovers.TwinQuotientFibres
import EPPAIII.CliqueCovers.OutsideTwinFibreLabel
import EPPAIII.CliqueCovers.ZeroPartialSpanning

/-!
# Zero-partial outside graph is sK_t, without assuming a partition

Suppose every outside neighbourhood profile meets each selected K_t
either entirely or not at all. For a non-cluster vertex-transitive
host of order 2st, the previously verified twin quotient argument
shows that it has 2s true-twin classes of size t; the s selected
classes are exactly the s base cliques. The remaining s quotient
classes can therefore be enumerated by Fin s and their fibres by
Fin t, producing a genuine equivalence Fin s × Fin t ≃ H\G.

Each labelled fibre consists of true twins, and hence is a clique.
The equal-half edge count excludes any further outside edges.
Thus H\G ≅ sK_t. This is precisely the partition lemma needed to
apply Lemma 3.7 to the non-homogeneous zero-partial case.

This theorem does not yet classify the complete/empty cross-block
masks of the outside twin classes, and does not deal with the
homogeneous (cluster) host case.
-/

namespace EPPAIII.CliqueCovers

/-- The no-partial-neighbourhood case automatically gives an
outside decomposition into s complete graphs of order t. -/
theorem zero_partial_outside_eq_cliqueUnion_of_noncluster {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ label : (Fin s × Fin t) ≃ {w : W // w ∈ finiteOutside e},
      (outsideInducedGraph H e).comap label = cliqueUnion s t := by
  classical
  let i : Fin s := ⟨0,hs⟩
  let a : Fin t := ⟨0,ht⟩
  obtain ⟨hQCount,hExact⟩ :=
    zero_partial_exact_twin_size_of_noncluster
      H e he hNoPartial hs ht hOrder hTransitive hNonCluster i a
  have hAllSelected :
      ∀ j : Fin s, (closedTwinClass H (e (j,a))).card = t := by
    intro j
    exact (closedTwinClass_card_of_vertex_transitive
      H hTransitive (e (j,a)) (e (i,a))).trans hExact
  have hOutCount :
      (outsideTwinQuotientClasses H e a).card = s :=
    outsideTwinQuotientClasses_card H e he a hQCount
  let fibre : ∀ z : {q : ClosedTwinQuotient H //
      q ∈ outsideTwinQuotientClasses H e a},
      Fin t ≃ {v : W // Quotient.mk (closedTwinSetoid H) v = z.val} :=
    fun z => finEquivClosedTwinFibre
      H e i a hTransitive hExact z.val
  obtain ⟨label,hFibre⟩ :=
    exists_outside_twin_fibre_label
      H e he hNoPartial a hAllSelected hOutCount fibre
  refine ⟨label, ?_⟩
  exact outside_eq_cliqueUnion_of_transitive_twin_fibres
    H e he hs ht hTransitive label hFibre

end EPPAIII.CliqueCovers
