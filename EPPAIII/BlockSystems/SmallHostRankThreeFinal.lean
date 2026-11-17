import EPPAIII.BlockSystems.SmallHostStrictRankThree
import EPPAIII.BlockSystems.GraphTransport
import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.EPPA.OutsideCardinality

/-!
# Complete small-host rank-three reduction for arbitrary vertex types

If a transitive EPPA host H has at most twice as many vertices as
the designated base G, and if equality forces the automorphism group
of H to be primitive, then all ordered edges form one orbit and all
ordered distinct nonedges form one orbit.

The strict inequality follows from the regular orbital-graph
independence bound. For equality, the canonical balanced coordinates
are constructed from an arbitrary fixed induced embedding, and EPPA,
primitivity, and ordered pair orbits are transferred along that actual
vertex equivalence.

The conclusion includes the complete and edgeless graphs, where only
one of the two off-diagonal pair types is present.
-/

namespace EPPAIII.BlockSystems

/-- Primitivity of the full host automorphism action is preserved
when the vertex type is relabelled by an equivalence. -/
theorem primitive_pullback_equiv {X W : Type*}
    (H : SimpleGraph W) (φ : X ≃ W)
    (hPrim : IsPrimitiveAutAction H) :
    IsPrimitiveAutAction (pullbackGraph H φ) := by
  intro R hR hInv
  let S : W → W → Prop :=
    fun u v => R (φ.symm u) (φ.symm v)
  have hS : Equivalence S := by
    refine ⟨?_,?_,?_⟩
    · intro u
      exact hR.refl (φ.symm u)
    · intro u v huv
      exact hR.symm huv
    · intro u v w huv hvw
      exact hR.trans huv hvw
  have hInvariant :
      ∀ (q : Equiv.Perm W), IsGraphAutomorphism H q →
        ∀ u v : W, S u v ↔ S (q u) (q v) := by
    intro q hq u v
    let q' : Equiv.Perm X := (φ.trans q).trans φ.symm
    have hConj (x : X) : φ (q' x) = q (φ x) := by
      simp [q', Equiv.trans_apply]
    have hq' : IsGraphAutomorphism (pullbackGraph H φ) q' := by
      intro x y
      change H.Adj (φ x) (φ y) ↔
        H.Adj (φ (q' x)) (φ (q' y))
      rw [hConj x, hConj y]
      exact hq (φ x) (φ y)
    have hh := hInv q' hq' (φ.symm u) (φ.symm v)
    change R (φ.symm u) (φ.symm v) ↔
      R (q' (φ.symm u)) (q' (φ.symm v)) at hh
    simpa [S, q', Equiv.trans_apply] using hh
  rcases hPrim S hS hInvariant with hDiscrete | hUniversal
  · left
    intro x y hxy
    apply φ.injective
    have hh : S (φ x) (φ y) := by
      simpa [S] using hxy
    exact hDiscrete (φ x) (φ y) hh
  · right
    intro x y
    have hh := hUniversal (φ x) (φ y)
    simpa [S] using hh

/-- Ordered edge/nonedge orbit transitivity transports from a
relabelled host back to the original vertex type. -/
theorem pair_orbits_of_pullback {X W : Type*}
    (H : SimpleGraph W) (φ : X ≃ W)
    (hPairs : HasOrderedPairOrbitByStatus (pullbackGraph H φ)) :
    HasOrderedPairOrbitByStatus H := by
  intro u v u' v' huv huv' hStatus
  have hxy : φ.symm u ≠ φ.symm v := by
    intro h
    exact huv (φ.symm.injective h)
  have hxy' : φ.symm u' ≠ φ.symm v' := by
    intro h
    exact huv' (φ.symm.injective h)
  have hStatus' :
      (pullbackGraph H φ).Adj (φ.symm u) (φ.symm v) ↔
        (pullbackGraph H φ).Adj (φ.symm u') (φ.symm v') := by
    change H.Adj (φ (φ.symm u)) (φ (φ.symm v)) ↔
      H.Adj (φ (φ.symm u')) (φ (φ.symm v'))
    simpa using hStatus
  obtain ⟨q,hq,hqu,hqv⟩ :=
    hPairs (φ.symm u) (φ.symm v)
      (φ.symm u') (φ.symm v') hxy hxy' hStatus'
  let qW : Equiv.Perm W := (φ.symm.trans q).trans φ
  have hqW : IsGraphAutomorphism H qW := by
    intro w z
    have hh := hq (φ.symm w) (φ.symm z)
    change H.Adj (φ (φ.symm w)) (φ (φ.symm z)) ↔
      H.Adj (φ (q (φ.symm w))) (φ (q (φ.symm z))) at hh
    simpa [qW, Equiv.trans_apply] using hh
  refine ⟨qW,hqW,?_,?_⟩
  · change φ (q (φ.symm u)) = u'
    rw [hqu]
    simp
  · change φ (q (φ.symm v)) = v'
    rw [hqv]
    simp

/-- Equality case for a *genuine arbitrary host* W, with no
pre-labelled second layer or assumption on the complementary graph.
The selected embedding is carried to the bottom of a canonical
balanced coordinate equivalence. -/
theorem transitive_eppa_primitive_double_has_pair_orbits
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hPrimitive : IsPrimitiveAutAction H)
    (hDouble : Fintype.card W = 2 * Fintype.card V) :
    HasOrderedPairOrbitByStatus H := by
  classical
  have hOutsideCard :
      (EPPAIII.finiteOutside e).card = Fintype.card V := by
    rw [EPPAIII.finiteOutside_card, hDouble]
    omega
  have hCard :
      Fintype.card V =
        Fintype.card {w : W // w ∈ EPPAIII.finiteOutside e} := by
    simpa only [Fintype.card_coe] using hOutsideCard.symm
  let outside : V ≃ {w : W // w ∈ EPPAIII.finiteOutside e} :=
    Fintype.equivOfCardEq hCard
  let φ : Bool × V ≃ W :=
    EPPAIII.CliqueCovers.balancedHostEquiv e outside
  have hBottom (x : V) : φ (false,x) = e x :=
    EPPAIII.CliqueCovers.balancedHostEquiv_false e outside x
  have hEPPA :
      IsEPPAEmbedding G (pullbackGraph H φ)
        (EPPAIII.DoubleCover.bottomEmbedding V) :=
    eppa_pullback_bottom G H e heppa φ hBottom
  have hGraph :
      pullbackGraph H φ = H.comap φ := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hTrans' :
      EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
        (pullbackGraph H φ) := by
    rw [hGraph]
    exact EPPAIII.CliqueCovers.transitive_comap_equiv H φ hTrans
  have hPrimitive' : IsPrimitiveAutAction (pullbackGraph H φ) :=
    primitive_pullback_equiv H φ hPrimitive
  have hPairs' : HasOrderedPairOrbitByStatus (pullbackGraph H φ) :=
    primitive_balanced_eppa_has_pair_orbits_all
      G (pullbackGraph H φ) hEPPA hTrans' hPrimitive'
  exact pair_orbits_of_pullback H φ hPairs'

/-- Exact source-facing Proposition prop:rank3, in its
ordered-pair-orbit formulation. Complete/empty graphs satisfy
the conclusion with one missing off-diagonal orbit. -/
theorem transitive_eppa_at_most_double_has_pair_orbits
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hPrimitiveIfDouble :
      Fintype.card W = 2 * Fintype.card V →
        IsPrimitiveAutAction H) :
    HasOrderedPairOrbitByStatus H := by
  by_cases hEq : Fintype.card W = 2 * Fintype.card V
  · exact transitive_eppa_primitive_double_has_pair_orbits
      G H e heppa hTrans (hPrimitiveIfDouble hEq) hEq
  · have hStrict : Fintype.card W < 2 * Fintype.card V := by
      omega
    exact transitive_eppa_small_strict_has_pair_orbits
      G H e heppa hTrans hStrict

end EPPAIII.BlockSystems
