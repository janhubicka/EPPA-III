import EPPAIII.DoubleCover.InducedTwoTransitiveCore

/-!
# 2-transitivity of the action induced on invariant EPPA fibres

There are two ordered-pair orbits initially, edges and nonedges,
and non-homogeneity implies that some induced automorphism
moves a pair across these types. Closing the induced actions
under inverses and composition merges the orbits.

This result requires only a genuine invariant pair system,
EPPA and non-homogeneity of the base. The Taylor-geometry
argument establishing pair invariance is a distinct obligation.
-/

namespace EPPAIII.DoubleCover

/-- An actual host automorphism together with its induced
permutation on the two-point fibres. -/
structure InducedFibreAut {V : Type*}
    (H : SimpleGraph (Bool × V)) where
  q : Equiv.Perm (Bool × V)
  σ : Equiv.Perm V
  hAut : IsGraphAutomorphism H q
  hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x

/-- Composition of two induced fibre actions. -/
def InducedFibreAut.comp {V : Type*} {H : SimpleGraph (Bool × V)}
    (A B : InducedFibreAut H) : InducedFibreAut H where
  q := A.q.trans B.q
  σ := A.σ.trans B.σ
  hAut := by
    intro u v
    exact (A.hAut u v).trans (B.hAut (A.q u) (A.q v))
  hBase := by
    intro b x
    change (B.q (A.q (b,x))).2 = B.σ (A.σ x)
    calc
      (B.q (A.q (b,x))).2 = B.σ ((A.q (b,x)).2) := by
        simpa using B.hBase (A.q (b,x)).1 (A.q (b,x)).2
      _ = B.σ (A.σ x) := by rw [A.hBase b x]

/-- Taking the inverse retains the induced fibre permutation. -/
def InducedFibreAut.inverse {V : Type*} {H : SimpleGraph (Bool × V)}
    (A : InducedFibreAut H) : InducedFibreAut H where
  q := A.q.symm
  σ := A.σ.symm
  hAut := by
    intro u v
    simpa using (A.hAut (A.q.symm u) (A.q.symm v)).symm
  hBase := by
    intro b x
    have h : A.σ ((A.q.symm (b,x)).2) = x := by
      calc
        A.σ ((A.q.symm (b,x)).2) =
            (A.q (A.q.symm (b,x))).2 := by
          simpa using
            (A.hBase (A.q.symm (b,x)).1 (A.q.symm (b,x)).2).symm
        _ = x := by simp
    apply A.σ.injective
    calc
      A.σ ((A.q.symm (b,x)).2) = x := h
      _ = A.σ (A.σ.symm x) := (A.σ.apply_symm_apply x).symm

/-- Transport equal-type ordered pairs by an induced action. -/
theorem induced_fibre_action_on_equal_type
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hType : G.Adj x y ↔ G.Adj u v) :
    ∃ A : InducedFibreAut H, A.σ x = u ∧ A.σ y = v := by
  obtain ⟨q,σ,hq,hσ,hx,hy⟩ :=
    eppa_induced_pair_orbit G H heppa hPairs
      x y u v hxy huv hType
  exact ⟨⟨q,σ,hq,hσ⟩,hx,hy⟩

/-- Under non-homogeneity some induced host action moves an
ordered base edge to an ordered base nonedge. -/
theorem induced_fibre_action_mixes_edge_to_nonedge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ (A : InducedFibreAut H) (x y : V),
      G.Adj x y ∧ ¬ G.Adj (A.σ x) (A.σ y) := by
  classical
  obtain ⟨q,σ,x,y,hq,hσ,hChanged⟩ :=
    induced_action_changes_some_pair_type
      G H heppa hPairs hNonhomogeneous
  let A : InducedFibreAut H := ⟨q,σ,hq,hσ⟩
  by_cases hEdge : G.Adj x y
  · have hNon : ¬ G.Adj (σ x) (σ y) := by
      intro h
      exact hChanged ⟨fun _ => h, fun _ => hEdge⟩
    exact ⟨A,x,y,hEdge,hNon⟩
  · have hImageEdge : G.Adj (σ x) (σ y) := by
      by_contra hNon
      exact hChanged
        ⟨fun h => False.elim (hEdge h),
          fun h => False.elim (hNon h)⟩
    refine ⟨A.inverse,σ x,σ y,hImageEdge,?_⟩
    change ¬ G.Adj (σ.symm (σ x)) (σ.symm (σ y))
    simpa using hEdge

/-- A finite non-homogeneous graph having an EPPA witness with an
invariant two-point fibre system induces a 2-transitive action
on the base indices. -/
theorem eppa_induced_fibre_action_two_transitive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph G)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ A : InducedFibreAut H, A.σ x = u ∧ A.σ y = v := by
  classical
  obtain ⟨C,a,b,hEdge,hCross⟩ :=
    induced_fibre_action_mixes_edge_to_nonedge
      G H heppa hPairs hNonhomogeneous
  have hab : a ≠ b := G.ne_of_adj hEdge
  have hcd : C.σ a ≠ C.σ b := C.σ.injective.ne hab
  by_cases hSource : G.Adj x y
  · by_cases hTarget : G.Adj u v
    · exact induced_fibre_action_on_equal_type
        G H heppa hPairs x y u v hxy huv
        (by simp [hSource,hTarget])
    · obtain ⟨A,hAx,hAy⟩ :=
        induced_fibre_action_on_equal_type G H heppa hPairs
          x y a b hxy hab (by simp [hSource,hEdge])
      obtain ⟨B,hBx,hBy⟩ :=
        induced_fibre_action_on_equal_type G H heppa hPairs
          (C.σ a) (C.σ b) u v hcd huv
          (by simp [hCross,hTarget])
      refine ⟨(A.comp C).comp B,?_,?_⟩
      · change B.σ (C.σ (A.σ x)) = u
        rw [hAx]
        exact hBx
      · change B.σ (C.σ (A.σ y)) = v
        rw [hAy]
        exact hBy
  · by_cases hTarget : G.Adj u v
    · obtain ⟨A,hAx,hAy⟩ :=
        induced_fibre_action_on_equal_type G H heppa hPairs
          x y (C.σ a) (C.σ b) hxy hcd
          (by simp [hSource,hCross])
      obtain ⟨B,hBx,hBy⟩ :=
        induced_fibre_action_on_equal_type G H heppa hPairs
          a b u v hab huv (by simp [hEdge,hTarget])
      refine ⟨(A.comp C.inverse).comp B,?_,?_⟩
      · change B.σ (C.σ.symm (A.σ x)) = u
        rw [hAx]
        simpa using hBx
      · change B.σ (C.σ.symm (A.σ y)) = v
        rw [hAy]
        simpa using hBy
    · exact induced_fibre_action_on_equal_type
        G H heppa hPairs x y u v hxy huv
        (by simp [hSource,hTarget])

end EPPAIII.DoubleCover
