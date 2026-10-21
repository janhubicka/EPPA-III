import EPPAIII.TwoGraphs.ReindexedTransversal

/-!
# Complementary one-point types: real EPPA extension

Unlike the equal-type case, the original bottom graph does not
admit the required partial swap. Use an actual separating EPPA
transversal, reindex it along the induced host fibre permutation,
and take its correctly relabelled graph. Complementary types
become equal in that graph, so EPPA extends the swap.
The resulting host automorphism descends to Aut of the original
two-graph. No coherent choice of EPPA extensions is assumed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- A Taylor EPPA witness with invariant fibres and a non-homogeneous
base can extend a one-point two-graph map in the complementary
adjacency-type case, fixing a prescribed finite set pointwise. -/
theorem eppa_one_point_extension_complementary_types
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (R : Finset V) (a b : V)
    (hab : a ≠ b) (ha : a ∉ R) (hb : b ∉ R)
    (hOpp : ∀ r ∈ R, G.Adj a r ↔ ¬ G.Adj b r) :
    ∃ τ : Equiv.Perm V,
      IsTwoGraphAutomorphism G τ ∧ τ a = b ∧
      (∀ r ∈ R, τ r = r) := by
  classical
  obtain ⟨q,hq,_,x,y,hAx,hBy,hSepXY⟩ :=
    taylor_separating_eppa_transversal_of_pairs
      G heppa hPairs hNonhomogeneous a b hab
  obtain ⟨σ,_,hBase⟩ :=
    taylor_host_action_inside_two_graph G hPairs q hq
  let e : V ↪ Bool × V := reindexedHostEmbedding q σ
  let t : V → Bool := fun z => (e z).1
  have hσx : σ x = a := (hBase false x).symm.trans hAx
  have hσy : σ y = b := (hBase false y).symm.trans hBy
  have hTa : t a = (q (false,x)).1 := by
    change (q (false,σ.symm a)).1 = (q (false,x)).1
    rw [←hσx]
    simp
  have hTb : t b = (q (false,y)).1 := by
    change (q (false,σ.symm b)).1 = (q (false,y)).1
    rw [←hσy]
    simp
  have hSep : t a ≠ t b := by
    rw [hTa,hTb]
    exact hSepXY
  let C : SimpleGraph V := G.comap σ.symm
  have hEppa : EPPAIII.IsEPPAEmbedding C
      (taylorPairGraph G) e :=
    eppa_reindexed_host_image G heppa q hq σ
  have hChoose (z : V) : e z = (t z,z) := by
    exact reindexed_host_choice q σ hBase z
  have hEqual : ∀ r ∈ R, C.Adj a r ↔ C.Adj b r := by
    intro r hr
    have hA := hEppa.1 a r
    have hB := hEppa.1 b r
    rw [hChoose a,hChoose r] at hA
    rw [hChoose b,hChoose r] at hB
    exact hA.trans
      ((taylor_complement_types_equal_on_transversal
        G t R a b ha hb hOpp hSep r hr).trans hB.symm)
  let p : Equiv.Perm V := Equiv.swap a b
  have hp : EPPAIII.IsPartialGraphAutomorphism C
      (insert a R) p :=
    equal_types_partial_swap C R a b ha hb hEqual
  obtain ⟨Q,hQ,hExt⟩ := hEppa.2 (insert a R) p hp
  obtain ⟨τ,hTwo,hQBase⟩ :=
    taylor_host_action_inside_two_graph G hPairs Q hQ
  have hPoint (z : V) (hz : z ∈ insert a R) :
      τ z = p z := by
    have hEz : (e z).2 = z := reindexed_host_fibre q σ hBase z
    have hEpz : (e (p z)).2 = p z :=
      reindexed_host_fibre q σ hBase (p z)
    calc
      τ z = τ ((e z).2) := congrArg τ hEz.symm
      _ = (Q (e z)).2 := (hQBase (e z).1 (e z).2).symm
      _ = (e (p z)).2 := congrArg Prod.snd (hExt z hz)
      _ = p z := hEpz
  refine ⟨τ,hTwo,?_,?_⟩
  · simpa [p] using hPoint a (by simp)
  · intro r hr
    have hFix : p r = r := by
      have hra : r ≠ a := by
        intro h; exact ha (h ▸ hr)
      have hrb : r ≠ b := by
        intro h; exact hb (h ▸ hr)
      exact Equiv.swap_apply_of_ne_of_ne hra hrb
    exact (hPoint r (Finset.mem_insert_of_mem hr)).trans hFix

/-- In both cases of the parity-type dichotomy, extend a one-point
two-graph partial map by an actual two-graph automorphism. -/
theorem eppa_one_point_two_graph_extension_of_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (R : Finset V) (a b : V)
    (hab : a ≠ b) (ha : a ∉ R) (hb : b ∉ R)
    (hParity : ∀ r ∈ R, ∀ s ∈ R,
      (OddBaseTriple G a r s ↔ OddBaseTriple G b r s)) :
    ∃ τ : Equiv.Perm V,
      IsTwoGraphAutomorphism G τ ∧ τ a = b ∧
      (∀ r ∈ R, τ r = r) := by
  rcases one_point_two_graph_types_uniform G a b R hParity with hEqual | hOpp
  · exact eppa_one_point_extension_equal_types
      G heppa hPairs R a b ha hb hEqual
  · exact eppa_one_point_extension_complementary_types
      G heppa hPairs hNonhomogeneous R a b hab ha hb hOpp

end EPPAIII.TwoGraphs
