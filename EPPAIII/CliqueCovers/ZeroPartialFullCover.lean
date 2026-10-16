import EPPAIII.CliqueCovers.ZeroPartialHostMaskGraph
import EPPAIII.CliqueCovers.ZeroPartialMaskCoverage
import EPPAIII.CliqueCovers.MaskCoverReindex

/-!
# Complete zero-partial classification for non-cluster EPPA witnesses

Let the designated induced graph be s disjoint K_t's and suppose
every outside neighbourhood slice is either empty or the whole
corresponding base clique. For a vertex-transitive non-cluster
double-sized EPPA witness:

1. the true-twin quotient has precisely s outside fibres of size t;
2. the outside half is sK_t, without any partition assumption;
3. the host is a masked clique cover, with one complete/empty
   mask for each true-twin fibre;
4. regularity makes all mask cardinalities equal;
5. EPPA realizes every mask of that fixed cardinality, hence
   the four finite normal forms exhaust the possibilities;
6. reindexing the outside fibres only, keeping the selected
   induced copy fixed, yields a uniform generalized clique cover.

No coherent extensions are assumed. The separate homogeneous
(cluster) host and low-parameter cases are not asserted here.
-/

namespace EPPAIII.CliqueCovers

/-- Full noncluster zero-partial statement of Lemma 3.7:
the entire host is a generalised clique cover in the canonical
selected/outside labelling, up to permuting outside classes. -/
theorem eppa_zero_partial_noncluster_host_is_uniform_cover_fixed_base {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y := by
  classical
  obtain ⟨label,hFibre,hOutside⟩ :=
    zero_partial_outside_twin_fibres_of_noncluster
      H e heppa.1 hNoPartial hs ht hOrder hTransitive hNonCluster
  let anchor : Fin t := ⟨0,ht⟩
  let mask : Fin s → Finset (Fin s) :=
    outsideMaskFamily H e anchor label
  have hGraph :
      H.comap (balancedHostEquiv e label) =
        maskCoverGraph s t mask :=
    zero_partial_host_eq_maskCoverGraph
      H e heppa.1 hNoPartial anchor label hFibre hOutside
  let i0 : Fin s := ⟨0,hs⟩
  let r : ℕ := (mask i0).card
  have hCard : ∀ i : Fin s, (mask i).card = r := by
    intro i
    exact zero_partial_outside_masks_uniform_of_transitive
      H e heppa.1 hNoPartial hs ht anchor label
      hFibre hOutside hTransitive i i0
  have hForms :
      (r = 0 ∧ ∀ i : Fin s, mask i = ∅) ∨
      (r = 1 ∧ ∃ p : Equiv.Perm (Fin s),
        ∀ i : Fin s, mask (p i) = {i}) ∨
      (r + 1 = s ∧ ∃ p : Equiv.Perm (Fin s),
        ∀ i : Fin s, mask (p i) =
          (Finset.univ : Finset (Fin s)).erase i) ∨
      (r = s ∧ ∀ i : Fin s,
        mask i = (Finset.univ : Finset (Fin s))) :=
    eppa_outside_twin_mask_family_four_forms
      H e heppa anchor label hFibre hs hCard
  obtain ⟨p,X,Y,hReindex⟩ :=
    maskCoverGraph_four_forms_up_to_right_reindex mask hForms
  let phi : CoverVertex s t ≃ W :=
    (rightCliqueReindex p).trans (balancedHostEquiv e label)
  refine ⟨phi,X,Y,?_,?_⟩
  · intro x
    change balancedHostEquiv e label (rightCliqueReindex p (false,x)) = e x
    simp [rightCliqueReindex]
  · change (H.comap (balancedHostEquiv e label)).comap
      (rightCliqueReindex p) = coverGraph s t X Y
    rw [hGraph]
    exact hReindex

/-- Original theorem, preserving the older API. The fixed-base form is
preferred for manuscript applications. -/
theorem eppa_zero_partial_noncluster_host_is_uniform_cover {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonCluster : ¬ EPPAIII.BlockSystems.IsClusterGraph H) :
    ∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      H.comap phi = coverGraph s t X Y := by
  obtain ⟨phi,X,Y,_,hEq⟩ :=
    eppa_zero_partial_noncluster_host_is_uniform_cover_fixed_base
      H e heppa hNoPartial hs ht hOrder hTransitive hNonCluster
  exact ⟨phi,X,Y,hEq⟩

end EPPAIII.CliqueCovers
