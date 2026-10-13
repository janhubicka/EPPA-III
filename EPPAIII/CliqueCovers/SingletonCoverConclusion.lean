import EPPAIII.CliqueCovers.SingletonCrossConnections
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# Complete generalised clique cover classification: singleton case

When one outside profile has a unique size-one coordinate, EPPA and
vertex-transitivity identify its outside vertices canonically with
Fin s × Fin t. The outside graph is sK_t, diagonal cross blocks are
matchings and all off-diagonal cross blocks have one common
complete/empty value. Gluing the actual base embedding and outside
equivalence gives a graph equality with Definition 1.6.

No a priori outside clique partition or coherent EPPA lifts are used.
-/

namespace EPPAIII.CliqueCovers

/-- The full vertex-transitive double-sized EPPA host is a uniform
generalised clique cover with diagonal matching in the singleton
one-partial case. The isomorphism is an explicit equivalence
Bool × Fin s × Fin t ≃ W, preserving the given base embedding. -/
theorem eppa_singleton_host_is_uniform_cover {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ b : Bool,
      H.comap
        (balancedHostEquiv e
          (saturatedSingletonOutsideEquiv
            H e heppa hOrder w hw hUnique)) =
        coverGraph s t .matching b := by
  classical
  obtain ⟨b,hCross⟩ :=
    eppa_singleton_cross_adj_uniform
      H e heppa hOrder w hw hUnique hs ht
  let label := saturatedSingletonOutsideEquiv
    H e heppa hOrder w hw hUnique
  have hOutside :=
    eppa_singleton_outside_eq_cliqueUnion_of_transitive
      H e heppa hOrder w hw hUnique hs ht hTransitive
  refine ⟨b, ?_⟩
  apply SimpleGraph.ext
  funext x y
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,c⟩⟩
  cases bx <;> cases cy
  · change H.Adj (e (i,a)) (e (j,c)) ↔
      (coverGraph s t .matching b).Adj
        (false,(i,a)) (false,(j,c))
    rw [left_induced]
    exact (heppa.1 (i,a) (j,c)).symm
  · change H.Adj (e (i,a)) (label (j,c)).val ↔
      (coverGraph s t .matching b).Adj
        (false,(i,a)) (true,(j,c))
    have hSym :
        H.Adj (e (i,a)) (label (j,c)).val ↔
          H.Adj (label (j,c)).val (e (i,a)) :=
      ⟨fun h => h.symm, fun h => h.symm⟩
    have hAdj := hSym.trans (hCross (j,c) i a)
    simpa [coverGraph, coverAdj, CrossType.rel, eq_comm] using hAdj
  · change H.Adj (label (i,a)).val (e (j,c)) ↔
      (coverGraph s t .matching b).Adj
        (true,(i,a)) (false,(j,c))
    simpa [coverGraph, coverAdj, CrossType.rel, eq_comm] using
      (hCross (i,a) j c)
  · change H.Adj (label (i,a)).val (label (j,c)).val ↔
      (coverGraph s t .matching b).Adj
        (true,(i,a)) (true,(j,c))
    rw [right_induced]
    change ((outsideInducedGraph H e).comap label).Adj (i,a) (j,c) ↔
      (cliqueUnion s t).Adj (i,a) (j,c)
    rw [hOutside]

end EPPAIII.CliqueCovers
