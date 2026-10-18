import EPPAIII.BlockSystems.FullDoubleCover

/-!
# Two-transitivity on the quotient of a two-point imprimitivity system

This is the first part of the last assertion of Lemma 5.12.
EPPA provides a transitive action of fibre-preserving host
automorphisms on ordered base edges and separately on ordered base
nonedges. If these two orbits did not coincide, every induced fibre
permutation would be a graph automorphism of the base. EPPA would
then force the base to be homogeneous. Thus for a non-homogeneous
base the induced action on fibres is 2-transitive.

We do not postulate a coherent lift of base permutations.
The orbit witnesses are actual host automorphisms; closure under
composition and inversion is proved below.
-/

namespace EPPAIII.DoubleCover

/-- An actual host graph automorphism which maps the ordered
pair of fibres indexed by x,y to those indexed by u,v. -/
def FibrePairReach {V : Type*}
    (H : SimpleGraph (Bool × V)) (x y u v : V) : Prop :=
  ∃ (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V),
    IsGraphAutomorphism H q ∧
    (∀ b : Bool, ∀ z : V, (q (b,z)).2 = σ z) ∧
    σ x = u ∧ σ y = v

theorem fibrePairReach_refl {V : Type*}
    (H : SimpleGraph (Bool × V)) (x y : V) :
    FibrePairReach H x y x y := by
  refine ⟨Equiv.refl _, Equiv.refl _, ?_, ?_, rfl, rfl⟩
  · intro u v
    rfl
  · intro b z
    rfl

theorem fibrePairReach_trans {V : Type*}
    (H : SimpleGraph (Bool × V)) (a b c d e f : V)
    (h₁ : FibrePairReach H a b c d)
    (h₂ : FibrePairReach H c d e f) :
    FibrePairReach H a b e f := by
  obtain ⟨q₁,σ₁,hq₁,hσ₁,ha,hb⟩ := h₁
  obtain ⟨q₂,σ₂,hq₂,hσ₂,hc,hd⟩ := h₂
  refine ⟨q₁.trans q₂, σ₁.trans σ₂, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (hq₁ u v).trans (hq₂ (q₁ u) (q₁ v))
  · intro t z
    change (q₂ (q₁ (t,z))).2 = σ₂ (σ₁ z)
    calc
      (q₂ (q₁ (t,z))).2 = σ₂ ((q₁ (t,z)).2) := by
        simpa using hσ₂ (q₁ (t,z)).1 (q₁ (t,z)).2
      _ = σ₂ (σ₁ z) := by rw [hσ₁ t z]
  · change σ₂ (σ₁ a) = e
    rw [ha,hc]
  · change σ₂ (σ₁ b) = f
    rw [hb,hd]

theorem fibrePairReach_symm {V : Type*}
    (H : SimpleGraph (Bool × V)) (a b c d : V)
    (h : FibrePairReach H a b c d) :
    FibrePairReach H c d a b := by
  obtain ⟨q,σ,hq,hσ,ha,hb⟩ := h
  have hqinv : IsGraphAutomorphism H q.symm := by
    intro u v
    simpa using (hq (q.symm u) (q.symm v)).symm
  have hσinv : ∀ (t : Bool) (z : V),
      (q.symm (t,z)).2 = σ.symm z := by
    intro t z
    apply σ.injective
    calc
      σ ((q.symm (t,z)).2) = (q (q.symm (t,z))).2 := by
        exact (hσ (q.symm (t,z)).1 (q.symm (t,z)).2).symm
      _ = z := by simp
      _ = σ (σ.symm z) := by simp
  refine ⟨q.symm,σ.symm,hqinv,hσinv,?_,?_⟩
  · apply σ.injective
    simpa using ha.symm
  · apply σ.injective
    simpa using hb.symm

/-- EPPA extensions of two-point isomorphisms act on the
corresponding ordered fibres with the same adjacency type. -/
theorem reach_of_same_base_type {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (a b c d : V) (hab : a ≠ b) (hcd : c ≠ d)
    (hType : G.Adj a b ↔ G.Adj c d) :
    FibrePairReach H a b c d := by
  obtain ⟨q,hq,hqa,hqb,_,_⟩ :=
    eppa_maps_two_fibres G H heppa hPairs a b c d hab hcd hType
  obtain ⟨σ,hσ⟩ := hPairs q hq
  refine ⟨q,σ,hq,hσ,?_,?_⟩
  · calc
      σ a = (q (false,a)).2 := (hσ false a).symm
      _ = c := by rw [hqa]
  · calc
      σ b = (q (false,b)).2 := (hσ false b).symm
      _ = d := by rw [hqb]

/-- If all induced permutations on the fibres preserve G, EPPA
forces G itself to be homogeneous. -/
theorem homogeneous_of_all_fibre_actions_preserve_base {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hAll : ∀ (q : Equiv.Perm (Bool × V))
      (σ : Equiv.Perm V), IsGraphAutomorphism H q →
      (∀ b : Bool, ∀ z : V, (q (b,z)).2 = σ z) →
      IsGraphAutomorphism G σ) :
    IsHomogeneousGraph G := by
  intro D p hPartial
  obtain ⟨q,hq,hExt⟩ := heppa.2 D p hPartial
  obtain ⟨σ,hσ⟩ := hPairs q hq
  refine ⟨σ,hAll q σ hq hσ,?_⟩
  intro x hx
  have h := hExt x hx
  have hs : (q (false,x)).2 = p x := congrArg Prod.snd h
  exact (hσ false x).symm.trans hs

/-- Non-homogeneity ensures that some actual host automorphism
induces a permutation that changes an adjacency type of G. -/
theorem exists_fibre_pair_type_change {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G) :
    ∃ a b c d : V,
      a ≠ b ∧ c ≠ d ∧
      ¬ (G.Adj a b ↔ G.Adj c d) ∧
      FibrePairReach H a b c d := by
  classical
  by_contra hNo
  apply hNonHomogeneous
  apply homogeneous_of_all_fibre_actions_preserve_base G H heppa hPairs
  intro q σ hq hσ x y
  by_cases hxy : x = y
  · subst y
    simp
  have hcd : σ x ≠ σ y := σ.injective.ne hxy
  by_contra hDiff
  apply hNo
  exact ⟨x,y,σ x,σ y,hxy,hcd,hDiff,
    q,σ,hq,hσ,rfl,rfl⟩

/-- The fibre-permutation action of a non-homogeneous EPPA
double cover is 2-transitive (on ordered pairs of distinct
fibres). It is the induced action of actual host automorphisms,
not an abstract extension group. -/
theorem eppa_fibre_action_two_transitive {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v) :
    FibrePairReach H x y u v := by
  classical
  by_cases hSame : G.Adj x y ↔ G.Adj u v
  · exact reach_of_same_base_type G H heppa hPairs
      x y u v hxy huv hSame
  obtain ⟨a,b,c,d,hab,hcd,hDifferent,hBridge⟩ :=
    exists_fibre_pair_type_change G H heppa hPairs hNonHomogeneous
  by_cases hMatch : G.Adj x y ↔ G.Adj a b
  · have hTarget : G.Adj c d ↔ G.Adj u v := by tauto
    exact fibrePairReach_trans H x y a b u v
      (reach_of_same_base_type G H heppa hPairs x y a b
        hxy hab hMatch)
      (fibrePairReach_trans H a b c d u v hBridge
        (reach_of_same_base_type G H heppa hPairs c d u v
          hcd huv hTarget))
  · have hSource : G.Adj x y ↔ G.Adj c d := by tauto
    have hTarget : G.Adj a b ↔ G.Adj u v := by tauto
    exact fibrePairReach_trans H x y c d u v
      (reach_of_same_base_type G H heppa hPairs x y c d
        hxy hcd hSource)
      (fibrePairReach_trans H c d a b u v
        (fibrePairReach_symm H a b c d hBridge)
        (reach_of_same_base_type G H heppa hPairs a b u v
          hab huv hTarget))

end EPPAIII.DoubleCover
