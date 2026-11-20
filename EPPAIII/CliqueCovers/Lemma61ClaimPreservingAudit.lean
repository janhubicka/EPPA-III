import EPPAIII.CliqueCovers.AllParametersClassification
import EPPAIII.CliqueCovers.ActualHostConclusion
import EPPAIII.CliqueCovers.ProperPartialPositions

/-!
# Lemma 6.1: independent case-by-case source-proof audit

This proof does not invoke the final `eppa_all_positive_clique_double_classification`
or the consolidated `eppa_noncluster_equal_clique_full_classification_fixed_base`.
It instead assembles the exact elementary and profile-case theorems that
justify the claim-preserving four-claim English rewrite.

The original lemma assumes both halves induce `sK_t`; the second half is
encoded by `outside` and `hOutside`. We do not need the manuscript's
additional imprimitive-host assumption.
-/

namespace EPPAIII.CliqueCovers

/-- The explicit cardinality trichotomy at the start of repaired Claim 6.2. -/
theorem lemma61_profile_cardinality_trichotomy
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (hs : 2 ≤ s) (ht : 2 ≤ t) :
    (properPartialPositions
       (finiteNeighbourhoodProfile H e w)).card = 0 ∨
    (properPartialPositions
       (finiteNeighbourhoodProfile H e w)).card = 1 ∨
    (s = 2 ∧ t = 2) :=
  eppa_proper_partial_trichotomy H e heppa hOrder w hw hs ht

/-- The exact arithmetic obstruction used for multiple partial coordinates. -/
theorem lemma61_multiple_partial_arithmetic
    (s t p : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hp : 2 ≤ p) (hps : p ≤ s)
    (hBudget : Nat.choose s p * t ^ p ≤ s * t) :
    s = 2 ∧ t = 2 ∧ p = 2 :=
  multiple_partial_orbit_arithmetic s t p hs ht hp hps hBudget

/-- Case-by-case proof of the original Lemma 6.1 conclusion, with its
actual chosen embedding fixed. The four English claims are justified
by the profile bounds, saturation, twin-quotient, and Wagner
normalization used in the individual branch lemmas. -/
theorem lemma61_claim_preserving_profile_audit
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (outside : (Fin s × Fin t) ≃
      {w : W // w ∈ finiteOutside e})
    (hOutside : (outsideInducedGraph H e).comap outside =
      cliqueUnion s t) :
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
      obtain ⟨phi,X,Y,hFixed,hEq⟩ :=
        eppa_independent_double_classification
          H e heppa hs (by simpa using hOrder)
          hTransitive outside hOutside
      exact Or.inl ⟨phi,X,Y,hFixed,hEq⟩
    · have ht2 : 2 ≤ t := by omega
      by_cases hCluster : EPPAIII.BlockSystems.IsClusterGraph H
      · exact Or.inl (eppa_cluster_actual_host_is_uniform_cover
          H e heppa hCluster outside hOutside)
      · -- The three profile regimes; no coherent EPPA lifts used.
        have hs : 2 ≤ s := hs2
        have ht : 2 ≤ t := ht2
        have hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H := hCluster
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
            refine ⟨rfl,rfl,phi,?_,hPhi⟩
            simpa using hFixed
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

end EPPAIII.CliqueCovers
