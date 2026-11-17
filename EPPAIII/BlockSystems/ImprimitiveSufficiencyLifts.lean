import EPPAIII.TwoGraphs.TransversalParity
import EPPAIII.BlockSystems.TwoCliqueTaylorNamed
import EPPAIII.EPPA.ComplementTransport
import EPPAIII.CliqueCovers.CoverAutomorphismLift

/-!
# Sufficiency certificates for homogeneous-base imprimitive models

All embeddings are the *actual* bottom-layer injections.  The
source-facing proofs never assert an automorphism lift is coherent.

This module proves the general lifting criterion and specializes it to
the separated double, the Taylor double, the twin blow-up, and matching
doubles (also with a complemented top layer).  An independent module
treats the unequal two-clique base, where homogeneity is false.
-/

namespace EPPAIII.BlockSystems

open EPPAIII.DoubleCover

/-- Sufficiency from extension of automorphisms of a homogeneous base.
The host automorphism need not be chosen coherently. -/
theorem eppa_of_homogeneous_base_and_lifts
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hInduced : IsInducedGraphEmbedding G H e)
    (hHomogeneous : IsHomogeneousGraph G)
    (hLift : ∀ σ : Equiv.Perm V,
      IsGraphAutomorphism G σ →
        ∃ q : Equiv.Perm W,
          IsGraphAutomorphism H q ∧
          ∀ x : V, q (e x) = e (σ x)) :
    IsEPPAEmbedding G H e := by
  refine ⟨hInduced, ?_⟩
  intro D p hp
  obtain ⟨σ, hσ, hAgree⟩ := hHomogeneous D p hp
  obtain ⟨q, hq, hBottom⟩ := hLift σ hσ
  refine ⟨q, hq, ?_⟩
  intro x hx
  exact (hBottom x).trans (congrArg e (hAgree x hx))

/-- The version for an actual bottom copy and *diagonal* base lifts. -/
theorem eppa_of_homogeneous_base_and_diagonal_lifts
    {V : Type*}
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (hInduced : IsInducedGraphEmbedding G H (bottomEmbedding V))
    (hHomogeneous : IsHomogeneousGraph G)
    (hDiagonal : ∀ σ : Equiv.Perm V,
      IsGraphAutomorphism G σ →
      IsGraphAutomorphism H
        (Equiv.prodCongr (Equiv.refl Bool) σ)) :
    IsEPPAEmbedding G H (bottomEmbedding V) := by
  apply eppa_of_homogeneous_base_and_lifts G H
    (bottomEmbedding V) hInduced hHomogeneous
  intro σ hσ
  refine ⟨Equiv.prodCongr (Equiv.refl Bool) σ,
    hDiagonal σ hσ, ?_⟩
  intro x
  rfl

/-- Two *disconnected* induced copies of the base, with a fixed
selected first half. -/
def separatedDoubleGraph {V : Type*}
    (G : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj u v := u.1 = v.1 ∧ G.Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact G.irrefl h.2

/-- A homogeneous graph has its separated double as an EPPA witness. -/
theorem homogeneous_base_separated_double_eppa
    {V : Type*}
    (G : SimpleGraph V) (hHom : IsHomogeneousGraph G) :
    IsEPPAEmbedding G (separatedDoubleGraph G) (bottomEmbedding V) := by
  apply eppa_of_homogeneous_base_and_diagonal_lifts G
    (separatedDoubleGraph G) ?_ hHom ?_
  · intro x y
    change G.Adj x y ↔ (false = false ∧ G.Adj x y)
    simp
  · intro σ hσ u v
    change (u.1 = v.1 ∧ G.Adj u.2 v.2) ↔
      (u.1 = v.1 ∧ G.Adj (σ u.2) (σ v.2))
    exact and_congr Iff.rfl (hσ u.2 v.2)

/-- The two-fold independent twin blow-up: same adjacency in all
four layer positions, and the two mates remain nonadjacent. -/
def twinBlowupGraph {V : Type*}
    (G : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj u v := G.Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact h.symm
  loopless := by
    constructor
    intro u h
    exact G.irrefl h

/-- Twin blow-ups have EPPA whenever the selected graph is homogeneous. -/
theorem homogeneous_base_twin_blowup_eppa
    {V : Type*}
    (G : SimpleGraph V) (hHom : IsHomogeneousGraph G) :
    IsEPPAEmbedding G (twinBlowupGraph G) (bottomEmbedding V) := by
  apply eppa_of_homogeneous_base_and_diagonal_lifts G
    (twinBlowupGraph G) ?_ hHom ?_
  · intro x y
    rfl
  · intro σ hσ u v
    change G.Adj u.2 v.2 ↔ G.Adj (σ u.2) (σ v.2)
    exact hσ u.2 v.2

/-- The canonical Taylor double is EPPA when the *base graph* itself
is homogeneous, independently of the two-graph classification. -/
theorem homogeneous_base_taylor_double_eppa
    {V : Type*}
    (G : SimpleGraph V) (hHom : IsHomogeneousGraph G) :
    IsEPPAEmbedding G (taylorPairGraph G) (bottomEmbedding V) := by
  apply eppa_of_homogeneous_base_and_diagonal_lifts G
    (taylorPairGraph G) ?_ hHom ?_
  · intro x y
    change G.Adj x y ↔ (x ≠ y ∧ (G.Adj x y ↔ false = false))
    constructor
    · intro h
      exact ⟨G.ne_of_adj h, by simp [h]⟩
    · intro h
      exact h.2.mpr rfl
  · intro σ hσ u v
    rcases u with ⟨b,x⟩
    rcases v with ⟨c,y⟩
    change (x ≠ y ∧ (G.Adj x y ↔ b = c)) ↔
      (σ x ≠ σ y ∧ (G.Adj (σ x) (σ y) ↔ b = c))
    constructor
    · rintro ⟨hxy,hRel⟩
      exact ⟨σ.injective.ne hxy, (hσ x y).symm.trans hRel⟩
    · rintro ⟨hxy,hRel⟩
      exact ⟨(fun heq => hxy (congrArg σ heq)),
        (hσ x y).trans hRel⟩

/-- A matching joins the two layers, whose top graph may differ
from the bottom graph. This includes ordinary prisms and the mixed
rook/complement-rook matching model. -/
def matchedLayerGraph {V : Type*}
    (G K : SimpleGraph V) : SimpleGraph (Bool × V) where
  Adj u v :=
    (u.1 = v.1 ∧
      (if u.1 then K.Adj u.2 v.2 else G.Adj u.2 v.2)) ∨
    (u.1 ≠ v.1 ∧ u.2 = v.2)
  symm := by
    constructor
    intro u v h
    rcases h with hSame | hCross
    · left
      refine ⟨hSame.1.symm, ?_⟩
      rw [← hSame.1]
      cases hb : u.1 with
      | false =>
          have ha : G.Adj u.2 v.2 := by
            simpa [hb] using hSame.2
          simpa [hb] using ha.symm
      | true =>
          have ha : K.Adj u.2 v.2 := by
            simpa [hb] using hSame.2
          simpa [hb] using ha.symm
    · exact Or.inr ⟨hCross.1.symm, hCross.2.symm⟩
  loopless := by
    constructor
    intro u h
    rcases h with hSame | hCross
    · cases hb : u.1 with
      | false =>
          exact G.irrefl (by simpa [hb] using hSame.2)
      | true =>
          exact K.irrefl (by simpa [hb] using hSame.2)
    · exact hCross.1 rfl

/-- A matching host is EPPA if the top-layer adjacency relation is
invariant under every automorphism of the homogeneous bottom graph. -/
theorem matched_layer_eppa_of_invariant_top
    {V : Type*}
    (G K : SimpleGraph V)
    (hHom : IsHomogeneousGraph G)
    (hTop : ∀ σ : Equiv.Perm V,
      IsGraphAutomorphism G σ →
      IsGraphAutomorphism K σ) :
    IsEPPAEmbedding G (matchedLayerGraph G K)
      (bottomEmbedding V) := by
  apply eppa_of_homogeneous_base_and_diagonal_lifts G
    (matchedLayerGraph G K) ?_ hHom ?_
  · intro x y
    change G.Adj x y ↔
      ((false = false ∧ (if false then K.Adj x y else G.Adj x y)) ∨
       (false ≠ false ∧ x = y))
    simp
  · intro σ hσ u v
    let hK : IsGraphAutomorphism K σ := hTop σ hσ
    have hLayer :
        (if u.1 then K.Adj u.2 v.2 else G.Adj u.2 v.2) ↔
        (if u.1 then K.Adj (σ u.2) (σ v.2)
          else G.Adj (σ u.2) (σ v.2)) := by
      cases hb : u.1 with
      | false => simpa [hb] using (hσ u.2 v.2)
      | true => simpa [hb] using (hK u.2 v.2)
    have hMate : u.2 = v.2 ↔ σ u.2 = σ v.2 := by
      constructor
      · intro h
        exact congrArg σ h
      · intro h
        exact σ.injective h
    change
      ((u.1 = v.1 ∧
          (if u.1 then K.Adj u.2 v.2 else G.Adj u.2 v.2)) ∨
        (u.1 ≠ v.1 ∧ u.2 = v.2)) ↔
      ((u.1 = v.1 ∧
          (if u.1 then K.Adj (σ u.2) (σ v.2)
           else G.Adj (σ u.2) (σ v.2))) ∨
        (u.1 ≠ v.1 ∧ σ u.2 = σ v.2))
    exact or_congr (and_congr Iff.rfl hLayer)
      (and_congr Iff.rfl hMate)

/-- Any homogeneous base has a matching prism as an EPPA witness. -/
theorem homogeneous_base_matching_prism_eppa
    {V : Type*}
    (G : SimpleGraph V) (hHom : IsHomogeneousGraph G) :
    IsEPPAEmbedding G (matchedLayerGraph G G) (bottomEmbedding V) := by
  apply matched_layer_eppa_of_invariant_top G G hHom
  intro σ hσ
  exact hσ

/-- The mixed G/G-complement matching double is likewise EPPA.
Its *transitivity* also needs a self-complementing base bijection. -/
theorem homogeneous_base_complement_matching_eppa
    {V : Type*}
    (G : SimpleGraph V) (hHom : IsHomogeneousGraph G) :
    IsEPPAEmbedding G (matchedLayerGraph G Gᶜ) (bottomEmbedding V) := by
  apply matched_layer_eppa_of_invariant_top G Gᶜ hHom
  intro σ hσ
  exact graphAutomorphism_complement G σ hσ

end EPPAIII.BlockSystems
