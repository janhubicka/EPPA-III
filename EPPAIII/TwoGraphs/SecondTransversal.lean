import EPPAIII.TwoGraphs.TaylorTwoGraphGroup
import EPPAIII.DoubleCover.InducedTwoTransitiveCore

/-!
# EPPA transversals and the first genuine Section 5 separation step

The image of an EPPA embedding under a host automorphism remains an
EPPA embedding. If a Taylor double of a non-homogeneous graph is EPPA
and has invariant natural fibres, some host automorphism sends the
bottom transversal to one which chooses *both* layers.

The conclusion is about actual automorphisms and actual EPPA
embeddings; it does not assume a chosen switching function or
coherent extensions.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- The induced embedding transported by a host permutation. -/
def hostImageEmbedding {V W : Type*}
    (e : V ↪ W) (q : Equiv.Perm W) : V ↪ W where
  toFun := fun x => q (e x)
  inj' := by
    intro x y h
    exact e.injective (q.injective h)

/-- An actual automorphism of the host transports every EPPA
embedding to another EPPA embedding with the *same* source graph.
No transitivity or fibre hypothesis is involved. -/
theorem eppa_embedding_of_host_image
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (heppa : EPPAIII.IsEPPAEmbedding G H e)
    (q : Equiv.Perm W)
    (hq : EPPAIII.IsGraphAutomorphism H q) :
    EPPAIII.IsEPPAEmbedding G H (hostImageEmbedding e q) := by
  constructor
  · intro x y
    exact (heppa.1 x y).trans (hq (e x) (e y))
  · intro D p hp
    obtain ⟨r,hr,hExt⟩ := heppa.2 D p hp
    let r' : Equiv.Perm W := (q.symm.trans r).trans q
    have hr' : EPPAIII.IsGraphAutomorphism H r' := by
      intro u v
      change H.Adj u v ↔
        H.Adj (q (r (q.symm u))) (q (r (q.symm v)))
      simpa using
        (((hq (q.symm u) (q.symm v)).symm).trans
          ((hr (q.symm u) (q.symm v)).trans
            (hq (r (q.symm u)) (r (q.symm v)))))
    refine ⟨r',hr',?_⟩
    intro x hx
    change q (r (q.symm (q (e x)))) = q (e (p x))
    rw [Equiv.symm_apply_apply]
    exact congrArg q (hExt x hx)

/-- A Taylor automorphism whose induced permutation changes a
base adjacency type cannot preserve a constant layer choice
on the selected bottom copy. -/
theorem taylor_changed_pair_forces_mixed_sides
    {V : Type*}
    (G : SimpleGraph V)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hq : EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q)
    (hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (x y : V)
    (hChanged : ¬ (G.Adj x y ↔ G.Adj (σ x) (σ y))) :
    (q (false,x)).1 ≠ (q (false,y)).1 := by
  intro hSame
  apply hChanged
  have hSource : G.Adj x y ↔
      (taylorPairGraph G).Adj (false,x) (false,y) := by
    change G.Adj x y ↔ (x ≠ y ∧ (G.Adj x y ↔ false = false))
    simp only [iff_true]
    constructor
    · intro h
      exact ⟨G.ne_of_adj h,h⟩
    · exact fun h => h.2
  have hTarget :
      (taylorPairGraph G).Adj (q (false,x)) (q (false,y)) ↔
        G.Adj (σ x) (σ y) := by
    change
      ((q (false,x)).2 ≠ (q (false,y)).2 ∧
       (G.Adj (q (false,x)).2 (q (false,y)).2 ↔
        (q (false,x)).1 = (q (false,y)).1)) ↔
      G.Adj (σ x) (σ y)
    rw [hBase false x, hBase false y, hSame]
    simp only [iff_true]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨G.ne_of_adj h,h⟩
  exact hSource.trans ((hq (false,x) (false,y)).trans hTarget)

/-- Non-homogeneity forces a genuinely mixed EPPA transversal:
there exists a host automorphism taking two selected vertices to
opposite sides of the natural two-point fibres. -/
theorem taylor_second_eppa_transversal_of_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (heppa : EPPAIII.IsEPPAEmbedding G
      (taylorPairGraph G) (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) ∧
      (∃ x y : V,
        (q (false,x)).1 ≠ (q (false,y)).1) ∧
      EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
        (hostImageEmbedding (bottomEmbedding V) q) := by
  obtain ⟨q,σ,x,y,hq,hBase,hChanged⟩ :=
    induced_action_changes_some_pair_type G (taylorPairGraph G)
      heppa hPairs hNonhomogeneous
  refine ⟨q,σ,hq,hBase,⟨x,y,?_⟩,?_⟩
  · exact taylor_changed_pair_forces_mixed_sides
      G q σ hq hBase x y hChanged
  · exact eppa_embedding_of_host_image G (taylorPairGraph G)
      (bottomEmbedding V) heppa q hq

/-- Source-facing version: the real EPPA fibre-rigidity theorem
supplies the invariant-pair hypothesis needed above. -/
theorem taylor_second_eppa_transversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    [Fintype (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableEq (EPPAIII.CliqueCovers.ClosedTwinQuotient (taylorPairGraph G))]
    [DecidableRel (EPPAIII.CliqueCovers.closedTwinQuotientGraph
      (taylorPairGraph G)).Adj]
    (heppa : EPPAIII.IsEPPAEmbedding G
      (taylorPairGraph G) (bottomEmbedding V))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (hEven : ∃ a b c : V, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      EvenTriple G a b c) :
    ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
      (∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x) ∧
      (∃ x y : V,
        (q (false,x)).1 ≠ (q (false,y)).1) ∧
      EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
        (hostImageEmbedding (bottomEmbedding V) q) := by
  exact taylor_second_eppa_transversal_of_pairs G heppa
    (taylor_eppa_intrinsic_fibres G heppa hNonhomogeneous hEven)
    hNonhomogeneous

end EPPAIII.TwoGraphs
