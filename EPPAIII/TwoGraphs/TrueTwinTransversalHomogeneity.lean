import EPPAIII.CliqueCovers.TwinQuotientAction
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# A true-twin transversal inherits homogeneity from EPPA

If the selected copy contains exactly one representative from
every true-twin class of an EPPA host, the base is isomorphic to
the canonical true-twin quotient. Every host automorphism
descends to the quotient, so EPPA extensions descend to genuine
automorphisms of the base.

This is the abstract and classification-free *second case* of the
true-twin quotient argument in Section 5 fibre rigidity.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- An EPPA base meeting every true-twin class exactly once must
be homogeneous. We spell this out as a complete condition on
the induced embedding rather than assuming quotient coordinates. -/
theorem eppa_twin_transversal_homogeneous
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hCovered : ∀ w : W,
      ∃ x : V, SameClosedNeighbourhood H w (e x))
    (hSeparated : ∀ x y : V,
      SameClosedNeighbourhood H (e x) (e y) → x = y) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  classical
  let π : V → ClosedTwinQuotient H :=
    fun x => Quotient.mk (closedTwinSetoid H) (e x)
  have hπInj : Function.Injective π := by
    intro x y h
    exact hSeparated x y (Quotient.exact h)
  have hπSurj : Function.Surjective π := by
    intro z
    induction z using Quotient.inductionOn with
    | _ w =>
      obtain ⟨x,hSame⟩ := hCovered w
      refine ⟨x,?_⟩
      change Quotient.mk (closedTwinSetoid H) (e x) =
        Quotient.mk (closedTwinSetoid H) w
      exact Quotient.sound hSame.symm
  let φ : V ≃ ClosedTwinQuotient H :=
    Equiv.ofBijective π ⟨hπInj,hπSurj⟩
  have hφ (x : V) :
      φ x = Quotient.mk (closedTwinSetoid H) (e x) := rfl
  have hGraph (x y : V) :
      G.Adj x y ↔ (closedTwinQuotientGraph H).Adj (φ x) (φ y) := by
    rw [hφ x,hφ y,closedTwinQuotient_adj_mk]
    constructor
    · intro hXY
      refine ⟨?_,(heppa.1 x y).mp hXY⟩
      intro hTwin
      have hEq : x = y := hSeparated x y hTwin
      exact (G.ne_of_adj hXY) hEq
    · rintro ⟨_,hXY⟩
      exact (heppa.1 x y).mpr hXY
  intro D p hp
  obtain ⟨q,hq,hExtend⟩ := heppa.2 D p hp
  let Q := liftTwinAutomorphism H q hq
  let σ : Equiv.Perm V := (φ.trans Q).trans φ.symm
  have hφσ (x : V) : φ (σ x) = Q (φ x) := by
    simp [σ]
  have hσAut : IsGraphAutomorphism G σ := by
    intro x y
    calc
      G.Adj x y ↔
        (closedTwinQuotientGraph H).Adj (φ x) (φ y) :=
          hGraph x y
      _ ↔ (closedTwinQuotientGraph H).Adj
        (Q (φ x)) (Q (φ y)) :=
          liftTwinAutomorphism_graphAut H q hq (φ x) (φ y)
      _ ↔ (closedTwinQuotientGraph H).Adj
        (φ (σ x)) (φ (σ y)) := by rw [hφσ x,hφσ y]
      _ ↔ G.Adj (σ x) (σ y) := (hGraph (σ x) (σ y)).symm
  refine ⟨σ,hσAut,?_⟩
  intro x hx
  have hQ : Q (φ x) = φ (p x) := by
    rw [hφ x, liftTwinAutomorphism_mk]
    have h := hExtend x hx
    rw [h]
    exact (hφ (p x)).symm
  apply φ.injective
  calc
    φ (σ x) = Q (φ x) := hφσ x
    _ = φ (p x) := hQ

/-- Equivalent one-sentence formulation with a unique selected
representative in each true-twin class. -/
theorem eppa_unique_twin_representatives_homogeneous
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hUnique : ∀ w : W,
      ∃! x : V, SameClosedNeighbourhood H w (e x)) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  apply eppa_twin_transversal_homogeneous G H e heppa
  · intro w
    obtain ⟨x,hx,_⟩ := hUnique w
    exact ⟨x,hx⟩
  · intro x y hSame
    obtain ⟨z,_,hUniq⟩ := hUnique (e x)
    have hx : x = z := hUniq x rfl
    have hy : y = z := hUniq y hSame
    exact hx.trans hy.symm

end EPPAIII.TwoGraphs
