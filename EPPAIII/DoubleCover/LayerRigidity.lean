import Mathlib

/-!
# Rigidity of the layers of an invariant two-point fibre system

This isolates the group-theoretic step used to exclude the
one-edge and three-edge configurations in Section 3. The
"exceptional relation" can be the unique edge or unique
nonedge between two fibres. If it is invariant, always joins
vertices on the same layer, and occurs between every pair of
distinct fibres, then a fibre-preserving automorphism cannot
change the layer on only some fibres.

This theorem does not assume anything about the particular graph
producing the exceptional relation. Instantiating it with
the explicit one-edge/three-edge matrices is the remaining bridge.
-/

namespace EPPAIII.DoubleCover

/-- A permutation taking each pair into one pair has opposite first
coordinates on the images of its two fibre mates. -/
theorem fibre_layer_complement {V : Type*}
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (x : V) :
    (q (true, x)).1 = !(q (false, x)).1 := by
  have hne : (q (true, x)).1 ≠ (q (false, x)).1 := by
    intro hfirst
    have hsecond : (q (true, x)).2 = (q (false, x)).2 := by
      simpa [hFibre]
    have hp : q (true, x) = q (false, x) := Prod.ext hfirst hsecond
    have he : (true, x) = (false, x) := q.injective hp
    cases he
  cases hf : (q (false, x)).1 <;> cases ht : (q (true, x)).1 <;>
    simp_all

/-- The exceptional pair relation forces every fibre to have the same
flip status under a fibre-preserving automorphism. -/
theorem uniform_layer_of_exceptional {V : Type*}
    (R : (Bool × V) → (Bool × V) → Prop)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (hPreserve : ∀ u v, R u v ↔ R (q u) (q v))
    (hExists : ∀ x y : V, x ≠ y → ∃ b : Bool, R (b, x) (b, y))
    (hSame : ∀ u v, R u v → u.1 = v.1) :
    ∀ x y : V, (q (false, x)).1 = (q (false, y)).1 := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  obtain ⟨b, hb⟩ := hExists x y hxy
  have hs : (q (b, x)).1 = (q (b, y)).1 :=
    hSame _ _ ((hPreserve _ _).mp hb)
  cases b with
  | false => exact hs
  | true =>
      have hx := fibre_layer_complement q σ hFibre x
      have hy := fibre_layer_complement q σ hFibre y
      rw [hx, hy] at hs
      cases hfx : (q (false, x)).1 <;>
        cases hfy : (q (false, y)).1 <;> simp_all

/-- If one selected vertex stays in the bottom layer, then every
selected vertex stays in the bottom layer. -/
theorem all_bottom_of_one_bottom {V : Type*}
    (R : (Bool × V) → (Bool × V) → Prop)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (hPreserve : ∀ u v, R u v ↔ R (q u) (q v))
    (hExists : ∀ x y : V, x ≠ y → ∃ b : Bool, R (b, x) (b, y))
    (hSame : ∀ u v, R u v → u.1 = v.1)
    (x0 : V) (hx0 : (q (false, x0)).1 = false) :
    ∀ x : V, (q (false, x)).1 = false := by
  intro x
  calc
    (q (false, x)).1 = (q (false, x0)).1 :=
      uniform_layer_of_exceptional R q σ hFibre
        hPreserve hExists hSame x x0
    _ = false := hx0

/-- The exceptional inter-fibre relation for a graph: the unique edge
in the one-edge pattern, or the unique nonedge in the three-edge pattern. -/
def graphExceptional {V : Type*} (H : SimpleGraph (Bool × V))
    (high : Bool) (u v : Bool × V) : Prop :=
  u.2 ≠ v.2 ∧ (if high then ¬ H.Adj u v else H.Adj u v)

/-- A graph automorphism preserving the fibre system and the unique
inter-fibre edge/nonedge cannot flip individual fibres independently.
All graph-specific hypotheses are explicit; no existence of a hidden
canonical lift is assumed. -/
theorem graph_uniform_layer_of_exceptional {V : Type*}
    (H : SimpleGraph (Bool × V)) (high : Bool)
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hq : ∀ u v, H.Adj u v ↔ H.Adj (q u) (q v))
    (hFibre : ∀ (b : Bool) (x : V), (q (b, x)).2 = σ x)
    (hOccurs : ∀ x y : V, x ≠ y → ∃ b : Bool,
      if high then ¬ H.Adj (b, x) (b, y) else H.Adj (b, x) (b, y))
    (hSame : ∀ u v : Bool × V, u.2 ≠ v.2 →
      (if high then ¬ H.Adj u v else H.Adj u v) → u.1 = v.1) :
    ∀ x y : V, (q (false, x)).1 = (q (false, y)).1 := by
  have hproj (u : Bool × V) : (q u).2 = σ u.2 := by
    rcases u with ⟨b, x⟩
    exact hFibre b x
  have hPres : ∀ u v, graphExceptional H high u v ↔
      graphExceptional H high (q u) (q v) := by
    intro u v
    have hn : (u.2 ≠ v.2) ↔ ((q u).2 ≠ (q v).2) := by
      rw [hproj u, hproj v]
      constructor
      · intro h hh
        exact h (σ.injective hh)
      · intro h hh
        exact h (congrArg σ hh)
    change (u.2 ≠ v.2 ∧
      (if high then ¬ H.Adj u v else H.Adj u v)) ↔
      ((q u).2 ≠ (q v).2 ∧
        (if high then ¬ H.Adj (q u) (q v) else H.Adj (q u) (q v)))
    constructor
    · rintro ⟨ha, hb⟩
      refine ⟨hn.mp ha, ?_⟩
      cases high
      · exact (hq u v).mp hb
      · exact fun hc => hb ((hq u v).mpr hc)
    · rintro ⟨ha, hb⟩
      refine ⟨hn.mpr ha, ?_⟩
      cases high
      · exact (hq u v).mpr hb
      · exact fun hc => hb ((hq u v).mp hc)
  have hSource : ∀ x y : V, x ≠ y →
      ∃ b : Bool, graphExceptional H high (b, x) (b, y) := by
    intro x y hxy
    obtain ⟨b, hb⟩ := hOccurs x y hxy
    exact ⟨b, ⟨hxy, hb⟩⟩
  have hTarget : ∀ u v : Bool × V,
      graphExceptional H high u v → u.1 = v.1 := by
    intro u v hh
    exact hSame u v hh.1 hh.2
  exact uniform_layer_of_exceptional (graphExceptional H high)
    q σ hFibre hPres hSource hTarget

end EPPAIII.DoubleCover
