import EPPAIII.CliqueCovers.CoSingletonCrossConnections
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges

/-!
# Full generalised clique cover classification: co-singleton case

The canonical outside label (i,a) names the *omitted* vertex a from
the i-th base clique neighbourhood. The outside graph is sK_t by the
vertex-transitive EPPA theorem; off-diagonal connections share one
Boolean bit, and the diagonal connection is a co-matching.

The host is therefore isomorphic, by an equivalence preserving the
distinguished induced base embedding, to Definition 1.6 with diagonal
type coMatching. No outside clique partition was assumed.
-/

namespace EPPAIII.CliqueCovers

/-- In the one-partial co-singleton case, the complete host is a
uniform generalised clique cover with diagonal co-matchings. -/
theorem eppa_cosingleton_host_is_uniform_cover {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hUnique :
      (kPositions (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ b : Bool,
      H.comap
        (balancedHostEquiv e
          (saturatedCoSingletonOutsideEquiv
            H e heppa hOrder (by omega) w hw hUnique)) =
        coverGraph s t .coMatching b := by
  classical
  obtain ⟨b,hCross⟩ :=
    eppa_cosingleton_cross_adj_uniform
      H e heppa hOrder w hw hUnique hs ht
  let label := saturatedCoSingletonOutsideEquiv
    H e heppa hOrder (by omega) w hw hUnique
  have hOutside :=
    eppa_cosingleton_outside_eq_cliqueUnion_of_transitive
      H e heppa hOrder w hw hUnique hs ht hTransitive
  refine ⟨b, ?_⟩
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,c⟩⟩
  cases bx <;> cases cy
  · change H.Adj (e (i,a)) (e (j,c)) ↔
      (coverGraph s t .coMatching b).Adj
        (false,(i,a)) (false,(j,c))
    simpa [coverGraph, coverAdj, cliqueUnion] using
      (heppa.1 (i,a) (j,c)).symm
  · change H.Adj (e (i,a)) (label (j,c)).val ↔
      (coverGraph s t .coMatching b).Adj
        (false,(i,a)) (true,(j,c))
    have hSym :
        H.Adj (e (i,a)) (label (j,c)).val ↔
          H.Adj (label (j,c)).val (e (i,a)) :=
      ⟨fun h => h.symm, fun h => h.symm⟩
    have hAdj := hSym.trans (hCross (j,c) i a)
    simpa [coverGraph, coverAdj, CrossType.rel, eq_comm] using hAdj
  · change H.Adj (label (i,a)).val (e (j,c)) ↔
      (coverGraph s t .coMatching b).Adj
        (true,(i,a)) (false,(j,c))
    simpa [coverGraph, coverAdj, CrossType.rel, eq_comm] using
      (hCross (i,a) j c)
  · change H.Adj (label (i,a)).val (label (j,c)).val ↔
      (coverGraph s t .coMatching b).Adj
        (true,(i,a)) (true,(j,c))
    have hRight :
        H.Adj (label (i,a)).val (label (j,c)).val ↔
          (cliqueUnion s t).Adj (i,a) (j,c) := by
      change ((outsideInducedGraph H e).comap label).Adj (i,a) (j,c) ↔
        (cliqueUnion s t).Adj (i,a) (j,c)
      rw [hOutside]
    simpa [coverGraph, coverAdj, cliqueUnion] using hRight

end EPPAIII.CliqueCovers
