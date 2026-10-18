import EPPAIII.CliqueCovers.ZeroPartialFullCover

/-!
# Independent selected half: no proper partial profile coordinates

When t=1, a profile coordinate has cardinality zero or one.
Consequently the already certified zero-partial full-host theorem
classifies every non-cluster vertex-transitive double-sized EPPA
witness of sK₁ as a generalised clique cover, preserving the
distinguished embedded copy. No assumption on the outside half.
-/

namespace EPPAIII.CliqueCovers

/-- The t=1 case of the non-cluster generalised clique-cover theorem,
for any positive number s of singleton cliques. -/
theorem eppa_noncluster_independent_half_is_cover {s : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin 1) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s 1) H e)
    (hs : 0 < s)
    (hOrder : Fintype.card W = 2 * s)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ (phi : CoverVertex s 1 ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin 1, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s 1 X Y := by
  classical
  have hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 1 := by
    intro w _ j
    have hBound :
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card ≤ 1 := by
      have h := Finset.card_le_univ
        (profileSlice (finiteNeighbourhoodProfile H e w) j)
      simpa using h
    omega
  exact eppa_zero_partial_noncluster_host_is_uniform_cover_fixed_base
    H e heppa hNoPartial hs (by decide)
    (by simpa using hOrder) hTransitive hNonCluster

end EPPAIII.CliqueCovers
