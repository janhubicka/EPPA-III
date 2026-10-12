import EPPAIII.CliqueCovers.OutsideChoiceEquiv
import EPPAIII.EPPA.ProfileAction

/-!
# Transporting EPPA lifts to the complementary half

A base automorphism extending to a host automorphism stabilizes
the complement of the distinguished induced copy, in both directions.
Consequently it acts on the `Subtype` of outside vertices and is
an automorphism of the induced outside graph.

At a saturated orbit this action can be conjugated through the
*canonical* outside-choice equivalence.  This formalizes the
graph-transport infrastructure for the one-partial-coordinate and
Wagner cases of Section 3, without assuming that arbitrary choices
of EPPA lifts compose or that outside vertices already form cliques.

The action of a specific wreath permutation on the choice labels
requires a further equivariance lemma, not asserted here.
-/

namespace EPPAIII.CliqueCovers

/-- Restrict the host graph to vertices outside an embedded base. -/
noncomputable def outsideInducedGraph {V W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W) :
    SimpleGraph {u : W // u ∈ finiteOutside e} :=
  H.comap Subtype.val

/-- Any permutation of W that extends a permutation of the base
stabilizes the outside subtype, giving an actual permutation there. -/
noncomputable def outsideLiftPermutation {V W : Type*} [Fintype W]
    (e : V ↪ W) (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hCompat : ∀ v : V, q (e v) = e (p v)) :
    Equiv.Perm {u : W // u ∈ finiteOutside e} := by
  classical
  have hCompatInv (v : V) :
      q.symm (e v) = e (p.symm v) := by
    apply q.injective
    simpa using (hCompat (p.symm v)).symm
  refine
    { toFun := fun u => ⟨q u.val, ?_⟩
      invFun := fun u => ⟨q.symm u.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hu : u.val ∉ Set.range e := by
      simpa [finiteOutside] using u.property
    simpa [finiteOutside] using
      lift_preserves_outside e p q hCompat u.val hu
  · have hu : u.val ∉ Set.range e := by
      simpa [finiteOutside] using u.property
    simpa [finiteOutside] using
      lift_preserves_outside e p.symm q.symm hCompatInv u.val hu
  · intro u
    apply Subtype.ext
    simp
  · intro u
    apply Subtype.ext
    simp

/-- The restricted host permutation remains a graph automorphism. -/
theorem outsideLiftPermutation_graphAut {V W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : V ↪ W)
    (p : Equiv.Perm V) (q : Equiv.Perm W)
    (hCompat : ∀ v : V, q (e v) = e (p v))
    (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism (outsideInducedGraph H e)
      (outsideLiftPermutation e p q hCompat) := by
  intro u v
  change H.Adj u.val v.val ↔ H.Adj (q u.val) (q v.val)
  exact hq u.val v.val

/-- The graph on the saturated finite profile-choice labels,
pulled back from the actual host adjacency by the canonical
outside-vertex equivalence. -/
noncomputable def saturatedChoiceGraph {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    SimpleGraph (AdmissibleProfileChoice s t r k) :=
  H.comap (fun c =>
    ((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm c).val)

/-- Conjugate the restriction of an EPPA extension through the
saturated choice equivalence.  The result acts on formal choices. -/
noncomputable def saturatedChoiceLiftPermutation {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (p : Equiv.Perm (Fin s × Fin t)) (q : Equiv.Perm W)
    (hCompat : ∀ v, q (e v) = e (p v)) :
    Equiv.Perm (AdmissibleProfileChoice s t r k) :=
  (((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm).trans
      (outsideLiftPermutation e p q hCompat)).trans
        (saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat)

/-- Conjugation preserves graph automorphisms of the outside half. -/
theorem saturatedChoiceLiftPermutation_graphAut {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (p : Equiv.Perm (Fin s × Fin t)) (q : Equiv.Perm W)
    (hCompat : ∀ v, q (e v) = e (p v))
    (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism
      (saturatedChoiceGraph H e heppa hOrder w hw r k hR hSat)
      (saturatedChoiceLiftPermutation H e heppa hOrder
        w hw r k hR hSat p q hCompat) := by
  intro x y
  change
    H.Adj
      ((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm x).val
      ((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm y).val ↔
    H.Adj
      (q ((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm x).val)
      (q ((saturatedOutsideChoiceEquiv H e heppa hOrder w hw r k hR hSat).symm y).val)
  exact hq _ _

/-- EPPA supplies an automorphism of the choice graph for every
automorphism of the base.  No coherent lifting assumption is used. -/
theorem eppa_saturated_choice_graph_lifts_base {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (p : Equiv.Perm (Fin s × Fin t))
    (hp : IsGraphAutomorphism (cliqueUnion s t) p) :
    ∃ (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q)
      (hCompat : ∀ v, q (e v) = e (p v)),
      IsGraphAutomorphism
        (saturatedChoiceGraph H e heppa hOrder w hw r k hR hSat)
        (saturatedChoiceLiftPermutation H e heppa hOrder
          w hw r k hR hSat p q hCompat) := by
  obtain ⟨q, hq, hCompat⟩ :=
    eppa_lifts_total (cliqueUnion s t) H e heppa p hp
  exact ⟨q, hq, hCompat,
    saturatedChoiceLiftPermutation_graphAut
      H e heppa hOrder w hw r k hR hSat p q hCompat hq⟩

end EPPAIII.CliqueCovers
