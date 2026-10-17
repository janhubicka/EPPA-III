import EPPAIII.CliqueCovers.AllParametersClassification

/-!
# Equal clique unions in non-cluster hosts: no outside hypothesis

The source's final imprimitive Proposition 6.17 invokes the
generalized clique-cover conclusion for G=sK_t, without first
knowing that the induced graph on the other half is sK_t.

This theorem supplies precisely that missing interface:
if H is a vertex-transitive, non-cluster, double-sized EPPA
host of sK_t, for any positive s and t, then H itself
produces a correctly aligned generalized clique cover, or
the exceptional Wagner graph. No imprimitive partition and
no decomposition of the complementary half are assumed.

For s,t≥2 we apply the fully verified profile-orbit
classification. For s=1 complementation reduces to the
independent-set case. For t=1 regularity forces the
other half to be independent, without any prior hypothesis.
-/

namespace EPPAIII.CliqueCovers

/-- A direct classification applicable in Proposition 6.17
without the extraneous complementary-half hypothesis. -/
theorem eppa_noncluster_clique_double_all_positive
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y) ∨
    (∃ (hS : s = 2) (hT : t = 2)
        (phi : CoverVertex 2 2 ≃ W),
       (∀ x : Fin 2 × Fin 2,
          phi (false,x) =
            e (Fin.cast hS.symm x.1, Fin.cast hT.symm x.2)) ∧
       H.comap phi = wagnerCanonicalGraph) := by
  classical
  by_cases hS : s = 1
  · subst s
    obtain ⟨phi,X,hFixed,hEq⟩ :=
      eppa_one_clique_double_classification
        H e heppa ht (by simpa using hOrder) hTransitive
    exact Or.inl ⟨phi,X,false,hFixed,hEq⟩
  · have hs2 : 2 ≤ s := by omega
    by_cases hT : t = 1
    · subst t
      obtain ⟨outside,hOutside⟩ :=
        outside_of_transitive_one_vertex_cliques
          H e heppa.1 hs (by simpa using hOrder) hTransitive
      obtain ⟨phi,X,Y,hFixed,hEq⟩ :=
        eppa_independent_double_classification
          H e heppa hs (by simpa using hOrder)
          hTransitive outside hOutside
      exact Or.inl ⟨phi,X,Y,hFixed,hEq⟩
    · have ht2 : 2 ≤ t := by omega
      exact eppa_noncluster_equal_clique_full_classification_fixed_base
        H e heppa hs2 ht2 hOrder hTransitive hNonCluster

end EPPAIII.CliqueCovers
