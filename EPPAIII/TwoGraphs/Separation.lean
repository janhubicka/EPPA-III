import EPPAIII.TwoGraphs.SecondTransversal
import EPPAIII.DoubleCover.InducedTwoTransitiveAssembly

/-!
# Separating EPPA transversals in a Taylor double

Once a non-homogeneous EPPA base supplies a mixed image of the
bottom transversal, the induced 2-transitive fibre action transports
its two different layer choices to any prescribed pair.

The theorem produces an ACTUAL host automorphism and an ACTUAL
transported EPPA embedding for each pair; it is not just a Boolean
switching identity or a claim about an abstract orbit.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- For two transversals differing at two base indices, their
images under any fibre-preserving permutation cannot *both*
choose the same layer at those two fibres. -/
theorem two_transversals_separate_under_fibre_action
    {V : Type*}
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (s : V → Bool) (x y : V)
    (hDifferent : s x ≠ s y) :
    (q (false,x)).1 ≠ (q (false,y)).1 ∨
      (q (s x,x)).1 ≠ (q (s y,y)).1 := by
  have hFlipX := fibre_layer_complement q σ hBase x
  have hFlipY := fibre_layer_complement q σ hBase y
  cases hsx : s x <;> cases hsy : s y <;>
    cases hfx : (q (false,x)).1 <;>
    cases hfy : (q (false,y)).1 <;>
    simp_all

/-- Genuine separating EPPA transversal for each ordered pair.
This formulation indexes an EPPA copy by its original vertices,
so it needs no unverified identification of the induced switched
graph with the original labelled graph. -/
theorem taylor_separating_eppa_transversal_of_pairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (heppa : EPPAIII.IsEPPAEmbedding G
      (taylorPairGraph G) (bottomEmbedding V))
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (a b : V) (hab : a ≠ b) :
    ∃ q : Equiv.Perm (Bool × V),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
      EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
        (hostImageEmbedding (bottomEmbedding V) q) ∧
      ∃ x y : V,
        (q (false,x)).2 = a ∧
        (q (false,y)).2 = b ∧
        (q (false,x)).1 ≠ (q (false,y)).1 := by
  obtain ⟨q₀,σ₀,hq₀,hBase₀,⟨x,y,hDifferent⟩,_⟩ :=
    taylor_second_eppa_transversal_of_pairs
      G heppa hPairs hNonhomogeneous
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hDifferent rfl
  obtain ⟨A,hAx,hAy⟩ :=
    eppa_induced_fibre_action_two_transitive
      G (taylorPairGraph G) heppa hPairs hNonhomogeneous
      (σ₀ x) (σ₀ y) a b (σ₀.injective.ne hxy) hab
  let s : V → Bool := fun z => (q₀ (false,σ₀.symm z)).1
  have hs : s (σ₀ x) ≠ s (σ₀ y) := by
    simpa [s] using hDifferent
  have hSep := two_transversals_separate_under_fibre_action
    A.q A.σ A.hBase s (σ₀ x) (σ₀ y) hs
  rcases hSep with hFirst | hSecond
  · refine ⟨A.q,A.hAut,?_ ,σ₀ x,σ₀ y,?_,?_,hFirst⟩
    · exact eppa_embedding_of_host_image G (taylorPairGraph G)
        (bottomEmbedding V) heppa A.q A.hAut
    · exact (A.hBase false (σ₀ x)).trans hAx
    · exact (A.hBase false (σ₀ y)).trans hAy
  · let q₂ : Equiv.Perm (Bool × V) := q₀.trans A.q
    have hq₂ : EPPAIII.IsGraphAutomorphism
        (taylorPairGraph G) q₂ := by
      intro u v
      exact (hq₀ u v).trans (A.hAut (q₀ u) (q₀ v))
    have hq₀x : q₀ (false,x) = (s (σ₀ x),σ₀ x) := by
      apply Prod.ext
      · simp [s]
      · exact hBase₀ false x
    have hq₀y : q₀ (false,y) = (s (σ₀ y),σ₀ y) := by
      apply Prod.ext
      · simp [s]
      · exact hBase₀ false y
    have hSide :
        (q₂ (false,x)).1 ≠ (q₂ (false,y)).1 := by
      change (A.q (q₀ (false,x))).1 ≠
        (A.q (q₀ (false,y))).1
      rw [hq₀x,hq₀y]
      exact hSecond
    have hBx : (q₂ (false,x)).2 = a := by
      calc
        (q₂ (false,x)).2 = A.σ ((q₀ (false,x)).2) := by
          exact A.hBase (q₀ (false,x)).1 (q₀ (false,x)).2
        _ = A.σ (σ₀ x) := by rw [hBase₀ false x]
        _ = a := hAx
    have hBy : (q₂ (false,y)).2 = b := by
      calc
        (q₂ (false,y)).2 = A.σ ((q₀ (false,y)).2) := by
          exact A.hBase (q₀ (false,y)).1 (q₀ (false,y)).2
        _ = A.σ (σ₀ y) := by rw [hBase₀ false y]
        _ = b := hAy
    exact ⟨q₂,hq₂,
      eppa_embedding_of_host_image G (taylorPairGraph G)
        (bottomEmbedding V) heppa q₂ hq₂,
      x,y,hBx,hBy,hSide⟩

/-- Source-facing separation theorem with intrinsic Taylor
fibre-rigidity obtained from actual EPPA and the even-triple
witness. -/
theorem taylor_separating_eppa_transversal
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
      EvenTriple G a b c)
    (a b : V) (hab : a ≠ b) :
    ∃ q : Equiv.Perm (Bool × V),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q ∧
      EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
        (hostImageEmbedding (bottomEmbedding V) q) ∧
      ∃ x y : V,
        (q (false,x)).2 = a ∧
        (q (false,y)).2 = b ∧
        (q (false,x)).1 ≠ (q (false,y)).1 := by
  exact taylor_separating_eppa_transversal_of_pairs G heppa
    (taylor_eppa_intrinsic_fibres G heppa hNonhomogeneous hEven)
    hNonhomogeneous a b hab

end EPPAIII.TwoGraphs
