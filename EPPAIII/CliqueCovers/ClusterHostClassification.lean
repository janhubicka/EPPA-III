import EPPAIII.CliqueCovers.ClusterHostBlocks
import EPPAIII.CliqueCovers.MaskCoverReindex
import EPPAIII.CliqueCovers.WreathGenerators
import EPPAIII.EPPA.ProfileAction

/-!
# Cluster hosts: complete or perfectly paired clique blocks

Let both the selected and complementary halves induce sK_t.
If the entire host is a cluster graph and the first half has EPPA,
then the cross-block incidence is empty or a perfect matching.
This is independent of vertex-transitivity and all external
classifications.

The resulting isomorphism fixes the selected half pointwise.
-/

namespace EPPAIII.CliqueCovers

private theorem cluster_selected_within {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (he : IsInducedGraphEmbedding
      (cliqueUnion s t) H (coverLeftEmbedding s t))
    (i : Fin s) (a b : Fin t) (hab : a ≠ b) :
    H.Adj (left i a) (left i b) :=
  (he (i,a) (i,b)).mp ⟨rfl,hab⟩

private theorem cluster_outside_within {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (hRight : ∀ i j : Fin s, ∀ a b : Fin t,
      H.Adj (right i a) (right j b) ↔
        i = j ∧ a ≠ b)
    (i : Fin s) (a b : Fin t) (hab : a ≠ b) :
    H.Adj (right i a) (right i b) :=
  (hRight i i a b).mpr ⟨rfl,hab⟩

private theorem cluster_selected_separate {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (he : IsInducedGraphEmbedding
      (cliqueUnion s t) H (coverLeftEmbedding s t))
    (i j : Fin s) (a b : Fin t) (hij : i ≠ j) :
    ¬ H.Adj (left i a) (left j b) := by
  intro hab
  exact hij ((he (i,a) (j,b)).mpr hab).1

private theorem cluster_outside_separate {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (hRight : ∀ i j : Fin s, ∀ a b : Fin t,
      H.Adj (right i a) (right j b) ↔
        i = j ∧ a ≠ b)
    (i j : Fin s) (a b : Fin t) (hij : i ≠ j) :
    ¬ H.Adj (right i a) (right j b) := by
  intro hab
  exact hij ((hRight i j a b).mp hab).1

/-- The cross incidence becomes a full/empty mask model. -/
private theorem cluster_host_eq_maskCover {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (he : IsInducedGraphEmbedding
      (cliqueUnion s t) H (coverLeftEmbedding s t))
    (hRight : ∀ i j : Fin s, ∀ a b : Fin t,
      H.Adj (right i a) (right j b) ↔
        i = j ∧ a ≠ b)
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H) :
    H = maskCoverGraph s t
      (fun j => Finset.univ.filter (fun i => HasCrossBlockEdge H i j)) := by
  classical
  let mask : Fin s → Finset (Fin s) :=
    fun j => Finset.univ.filter (fun i => HasCrossBlockEdge H i j)
  have hCross (i j : Fin s) (a b : Fin t) :
      H.Adj (left i a) (right j b) ↔ i ∈ mask j := by
    constructor
    · intro hab
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨a,b,hab⟩⟩
    · intro hi
      exact cluster_cross_block_complete H hCluster
        (cluster_selected_within H he)
        (cluster_outside_within H hRight)
        i j (Finset.mem_filter.mp hi).2 a b
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨sx,⟨i,a⟩⟩
  rcases y with ⟨sy,⟨j,b⟩⟩
  cases sx <;> cases sy
  · change H.Adj (left i a) (left j b) ↔
        maskCoverAdj mask (false,(i,a)) (false,(j,b))
    simpa [maskCoverAdj,cliqueUnion] using (he (i,a) (j,b)).symm
  · change H.Adj (left i a) (right j b) ↔
        maskCoverAdj mask (false,(i,a)) (true,(j,b))
    simpa [maskCoverAdj] using hCross i j a b
  · change H.Adj (right i a) (left j b) ↔
        maskCoverAdj mask (true,(i,a)) (false,(j,b))
    have hh := (H.adj_comm (right i a) (left j b)).trans
      (hCross j i b a)
    simpa [maskCoverAdj] using hh
  · change H.Adj (right i a) (right j b) ↔
        maskCoverAdj mask (true,(i,a)) (true,(j,b))
    simpa [maskCoverAdj] using hRight i j a b

/-- Any existing cross-block edge can be moved to any prescribed
selected clique, by an actual EPPA lift of a base clique permutation. -/
private theorem cluster_cross_row_exists_of_eppa {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (heppa : IsEPPAEmbedding
      (cliqueUnion s t) H (coverLeftEmbedding s t))
    (i₀ i : Fin s)
    (h : ∃ j : Fin s, HasCrossBlockEdge H i₀ j) :
    ∃ j : Fin s, HasCrossBlockEdge H i j := by
  classical
  let p : Equiv.Perm (Fin s) := Equiv.swap i₀ i
  obtain ⟨q,hq,hCompat⟩ := eppa_lifts_total
    (cliqueUnion s t) H (coverLeftEmbedding s t) heppa
    (outerPermutation p) (outerPermutation_aut p)
  obtain ⟨j,a,b,hab⟩ := h
  have hLeft : q (left i₀ a) = left i a := by
    have hh := hCompat (i₀,a)
    simpa [coverLeftEmbedding,left,outerPermutation,p] using hh
  have hOutside : right j b ∉ Set.range (coverLeftEmbedding s t) := by
    rintro ⟨⟨k,c⟩,hk⟩
    exact Bool.false_ne_true (congrArg Prod.fst hk)
  have hAfter := lift_preserves_outside
    (coverLeftEmbedding s t) (outerPermutation p)
    q hCompat (right j b) hOutside
  rcases hImage : q (right j b) with ⟨side,⟨k,c⟩⟩
  cases side with
  | false =>
      exfalso
      apply hAfter
      exact ⟨(k,c),by simpa [coverLeftEmbedding] using hImage.symm⟩
  | true =>
      refine ⟨k,a,c,?_⟩
      have hEdge := (hq (left i₀ a) (right j b)).mp hab
      simpa [hLeft,hImage,left,right] using hEdge

/-- The exact cluster-host normal forms, preserving the chosen copy
of sK_t. In fact EPPA replaces vertex-transitivity in this case. -/
theorem eppa_cluster_host_full_or_empty {s t : ℕ}
    (H : SimpleGraph (CoverVertex s t))
    (heppa : IsEPPAEmbedding
      (cliqueUnion s t) H (coverLeftEmbedding s t))
    (hRight : ∀ i j : Fin s, ∀ a b : Fin t,
      H.Adj (right i a) (right j b) ↔
        i = j ∧ a ≠ b)
    (hCluster : EPPAIII.BlockSystems.IsClusterGraph H) :
    H = coverGraph s t .empty false ∨
      ∃ p : Equiv.Perm (Fin s),
        H.comap (rightCliqueReindex p) =
          coverGraph s t .full false := by
  classical
  let mask : Fin s → Finset (Fin s) :=
    fun j => Finset.univ.filter (fun i => HasCrossBlockEdge H i j)
  have hMasked : H = maskCoverGraph s t mask :=
    cluster_host_eq_maskCover H heppa.1 hRight hCluster
  by_cases hSome : ∃ i j : Fin s, HasCrossBlockEdge H i j
  · right
    obtain ⟨i₀,j₀,hEdge⟩ := hSome
    have hRows : ∀ i : Fin s, ∃ j : Fin s,
        HasCrossBlockEdge H i j := by
      intro i
      exact cluster_cross_row_exists_of_eppa
        H heppa i₀ i ⟨j₀,hEdge⟩
    let f : Fin s → Fin s := fun i => (hRows i).choose
    have hf (i : Fin s) : HasCrossBlockEdge H i (f i) :=
      (hRows i).choose_spec
    have hfInj : Function.Injective f := by
      intro i k hik
      apply cluster_cross_block_col_unique H hCluster
        (cluster_selected_within H heppa.1)
        (cluster_outside_within H hRight)
        (cluster_selected_separate H heppa.1)
        i k (f i) (hf i)
      simpa [hik] using hf k
    have hBij : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).2
        ⟨hfInj, by simp⟩
    let p : Equiv.Perm (Fin s) := Equiv.ofBijective f hBij
    have hp (i : Fin s) : mask (p i) = {i} := by
      ext k
      constructor
      · intro hk
        have hki : HasCrossBlockEdge H k (f i) :=
          (Finset.mem_filter.mp hk).2
        have hEq := cluster_cross_block_col_unique H hCluster
          (cluster_selected_within H heppa.1)
          (cluster_outside_within H hRight)
          (cluster_selected_separate H heppa.1)
          k i (f i) hki (hf i)
        simpa [hEq]
      · intro hk
        have hki : k = i := Finset.mem_singleton.mp hk
        subst k
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hf i⟩
    refine ⟨p,?_⟩
    rw [hMasked,maskCoverGraph_comap_rightCliqueReindex]
    have hMask : (fun j : Fin s => mask (p j)) =
        (fun j : Fin s => ({j} : Finset (Fin s))) :=
      funext hp
    rw [hMask]
    exact maskCoverGraph_singleton_eq_coverGraph s t
  · left
    have hEmpty : mask = fun _ => ∅ := by
      funext j
      ext i
      simp only [mask,Finset.mem_filter,Finset.mem_univ,true_and,
        Finset.not_mem_empty,iff_false]
      intro hij
      exact hSome ⟨i,j,hij⟩
    rw [hMasked,hEmpty]
    exact maskCoverGraph_empty_eq_coverGraph s t

end EPPAIII.CliqueCovers
