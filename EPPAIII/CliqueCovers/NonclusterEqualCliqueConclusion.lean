import EPPAIII.CliqueCovers.ProperPartialPositions
import EPPAIII.CliqueCovers.SingletonCoverConclusion
import EPPAIII.CliqueCovers.CoSingletonCoverConclusion
import EPPAIII.CliqueCovers.WagnerHostConclusion
import EPPAIII.CliqueCovers.ZeroPartialFullCover

/-!
# Non-cluster double-sized EPPA witnesses for equal cliques

Combines the formerly separate classification branches of Section 3
into one statement for s,t≥2 and non-cluster vertex-transitive hosts.

If some outside profile has a proper partial coordinate, either:
* it is the unique proper partial coordinate, with size 1 or t−1,
  and the complete one-partial host theorem gives a uniform
  generalized clique cover; or
* two distinct proper coordinates occur, forcing s=t=2, in which
  case the complete eight-vertex Wagner theorem applies.

If no outside profile has a proper coordinate, the noncluster
zero-partial host theorem gives a uniform generalized clique cover.

The complementary clique partition and all actions on outside
vertices are conclusions, not assumptions. No coherent EPPA lifts
are required. The low-parameter and homogeneous cases remain
separate formal obligations.
-/

namespace EPPAIII.CliqueCovers

/-- Main non-cluster equal-clique classification, with neither
an assumed complementary-half partition nor an imprimitivity
hypothesis. -/
theorem eppa_noncluster_equal_clique_full_classification_fixed_base {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
       (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
       H.comap phi = coverGraph s t X Y) ∨
    (s = 2 ∧ t = 2 ∧
      ∃ phi : CoverVertex 2 2 ≃ W,
        H.comap phi = wagnerCanonicalGraph) := by
  classical
  by_cases hSome :
      ∃ w : W, w ∉ Set.range e ∧
        (properPartialPositions
          (finiteNeighbourhoodProfile H e w)).Nonempty
  · obtain ⟨w,hw,⟨i,hi⟩⟩ := hSome
    let P : Finset (Fin s × Fin t) := finiteNeighbourhoodProfile H e w
    let S : Finset (Fin s) := properPartialPositions P
    have hPos : 0 < S.card := Finset.card_pos.mpr ⟨i,hi⟩
    by_cases hTwo : 2 ≤ S.card
    · obtain ⟨hs2,ht2⟩ :=
        eppa_two_proper_partial_positions_exception
          H e heppa hOrder w hw hs ht hTwo
      subst s
      subst t
      have hCard : S.card = 2 := by
        have hBound : S.card ≤ 2 := by
          have h := Finset.card_le_univ S
          simpa [S] using h
        omega
      have hFull : S = (Finset.univ : Finset (Fin 2)) := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simpa [hCard]
      have hEvery (j : Fin 2) :
          (profileSlice P j).card = 1 := by
        have hj : j ∈ S := by
          rw [hFull]
          exact Finset.mem_univ _
        obtain ⟨hp,hpProper⟩ :=
          (mem_properPartialPositions P j).mp hj
        omega
      have hK : kPositions P 1 = Finset.univ := by
        ext j
        simp only [Finset.mem_univ, iff_true]
        exact (mem_kPositions P 1 j).mpr (hEvery j)
      have hBoth :
          (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2 := by
        rw [hK]
        decide
      obtain ⟨phi,hFixed,hPhi⟩ :=
        eppa_two_partial_host_is_wagner_fixed_base
          H e heppa hOrder w hw hBoth hTransitive
      right
      exact ⟨rfl,rfl,phi,hPhi⟩
    · have hOne : S.card = 1 := by omega
      obtain ⟨j,k,hkPos,hkProper,hSlice,hUnique⟩ :=
        unique_proper_partial_gives_unique_k P hOne
      have hExtreme : k = 1 ∨ k + 1 = t :=
        eppa_clique_degree_extreme_of_double
          H e heppa hOrder w hw j k
            (by omega) hkPos hkProper hSlice
      rcases hExtreme with hkOne | hkCo
      · have hUniqueOne :
            (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 1 := by
          simpa [P,hkOne] using hUnique
        obtain ⟨b,hEq⟩ :=
          eppa_singleton_host_is_uniform_cover
            H e heppa hOrder w hw hUniqueOne hs ht hTransitive
        left
        refine ⟨balancedHostEquiv e
          (saturatedSingletonOutsideEquiv
            H e heppa hOrder w hw hUniqueOne),
            .matching,b,?_,hEq⟩
        intro x
        simp
      · have hkCosingleton : k = t - 1 := by omega
        have hUniqueCo :
            (kPositions
              (finiteNeighbourhoodProfile H e w) (t - 1)).card = 1 := by
          simpa [P,hkCosingleton] using hUnique
        obtain ⟨b,hEq⟩ :=
          eppa_cosingleton_host_is_uniform_cover
            H e heppa hOrder w hw hUniqueCo hs ht hTransitive
        left
        refine ⟨balancedHostEquiv e
          (saturatedCoSingletonOutsideEquiv
            H e heppa hOrder (by omega) w hw hUniqueCo),
            .coMatching,b,?_,hEq⟩
        intro x
        simp
  · have hNoPartial :
        ∀ w : W, w ∉ Set.range e →
          ∀ j : Fin s,
            (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
            (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t := by
      intro w hw j
      let P : Finset (Fin s × Fin t) :=
        finiteNeighbourhoodProfile H e w
      have hjNot : j ∉ properPartialPositions P := by
        intro hj
        exact hSome ⟨w,hw,⟨j,hj⟩⟩
      let k := (profileSlice P j).card
      have hBound : k ≤ t := by
        have h := Finset.card_le_univ (profileSlice P j)
        simpa [k] using h
      by_cases hZero : k = 0
      · exact Or.inl hZero
      · have hkPos : 0 < k := by omega
        have hkNotProper : ¬ k < t := by
          intro hkLt
          exact hjNot
            ((mem_properPartialPositions P j).mpr ⟨hkPos,hkLt⟩)
        have hkEq : k = t := by omega
        exact Or.inr hkEq
    obtain ⟨phi,X,Y,hFixed,hEq⟩ :=
      eppa_zero_partial_noncluster_host_is_uniform_cover_fixed_base
        H e heppa hNoPartial (by omega) (by omega)
        hOrder hTransitive hNonCluster
    exact Or.inl ⟨phi,X,Y,hFixed,hEq⟩

/-- The old public theorem follows by forgetting the fixed base copy. -/
theorem eppa_noncluster_equal_clique_full_classification {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
       H.comap phi = coverGraph s t X Y) ∨
    (s = 2 ∧ t = 2 ∧
      ∃ phi : CoverVertex 2 2 ≃ W,
        H.comap phi = wagnerCanonicalGraph) := by
  rcases eppa_noncluster_equal_clique_full_classification_fixed_base
      H e heppa hs ht hOrder hTransitive hNonCluster with hCover | hWagner
  · rcases hCover with ⟨phi,X,Y,_,hEq⟩
    exact Or.inl ⟨phi,X,Y,hEq⟩
  · rcases hWagner with ⟨hs2,ht2,phi,hEq⟩
    exact Or.inr ⟨hs2,ht2,phi,hEq⟩

end EPPAIII.CliqueCovers
