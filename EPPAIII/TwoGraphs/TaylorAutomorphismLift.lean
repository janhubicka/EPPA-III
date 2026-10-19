import EPPAIII.TwoGraphs.XorSwitchingPotential

/-!
# Elementary lifting of two-graph automorphisms to Taylor doubles

Any permutation preserving the parity of all base triples lifts to an
automorphism of the canonical Taylor double by an explicit switching
of the two fibre sides. No external Mallows--Sloane theorem is used.

The construction also gives the side bit of the image of every vertex
and leaves the projection to the base permutation unchanged.
-/

namespace EPPAIII.TwoGraphs

/-- The exact six-bit parity identity governing switching of an
edge between two Taylor fibres. -/
theorem xor_switch_adjacency
    (a af sx sy b c : Bool)
    (h : Bool.xor a af = Bool.xor sx sy) :
    (a = true ↔ b = c) ↔
      (af = true ↔ Bool.xor b sx = Bool.xor c sy) := by
  cases a <;> cases af <;> cases sx <;>
    cases sy <;> cases b <;> cases c <;>
    simp_all [Bool.xor]

/-- Every Boolean switching potential defines a permutation of the
canonical two-layer vertex type, covering the given base permutation. -/
def taylorSwitchLift {V : Type*}
    (f : Equiv.Perm V) (h : V → Bool) :
    Equiv.Perm (Bool × V) where
  toFun := fun u => (Bool.xor u.1 (h u.2), f u.2)
  invFun := fun u =>
    (Bool.xor u.1 (h (f.symm u.2)), f.symm u.2)
  left_inv := by
    rintro ⟨b,x⟩
    change (Bool.xor (Bool.xor b (h x)) (h (f.symm (f x))),
      f.symm (f x)) = (b,x)
    cases b <;> cases hh : h x <;> simp [hh, Bool.xor]
  right_inv := by
    rintro ⟨b,x⟩
    change (Bool.xor (Bool.xor b (h (f.symm x)))
      (h (f.symm x)), f (f.symm x)) = (b,x)
    cases b <;> cases hh : h (f.symm x) <;>
      simp [hh, Bool.xor]

/-- The XOR potential precisely ensures that the lift preserves
every edge and nonedge of the Taylor double. -/
theorem taylorSwitchLift_graphAut
    {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Equiv.Perm V) (h : V → Bool)
    (hDelta : ∀ x y : V,
      Bool.xor (decide (G.Adj x y))
        (decide (G.Adj (f x) (f y))) =
          Bool.xor (h x) (h y)) :
    EPPAIII.IsGraphAutomorphism (taylorPairGraph G)
      (taylorSwitchLift f h) := by
  intro u v
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  change (x ≠ y ∧ (G.Adj x y ↔ b = c)) ↔
    (f x ≠ f y ∧
      (G.Adj (f x) (f y) ↔
        Bool.xor b (h x) = Bool.xor c (h y)))
  have hh := xor_switch_adjacency
    (decide (G.Adj x y)) (decide (G.Adj (f x) (f y)))
    (h x) (h y) b c (hDelta x y)
  have hAdj :
      (G.Adj x y ↔ b = c) ↔
        (G.Adj (f x) (f y) ↔
          Bool.xor b (h x) = Bool.xor c (h y)) := by
    simpa only [decide_eq_true_eq] using hh
  constructor
  · rintro ⟨hxy,hbc⟩
    exact ⟨f.injective.ne hxy,hAdj.mp hbc⟩
  · rintro ⟨hxy,hbc⟩
    exact ⟨fun heq => hxy (congrArg f heq),hAdj.mpr hbc⟩

/-- Any automorphism of the odd-triple parity structure on the
base has an explicit lift to an automorphism of its Taylor double.
This is the full-automorphism half of the classical switching theorem
required in Section 5. -/
theorem taylor_automorphism_lift_of_triple_parity
    {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : Equiv.Perm V)
    (hTriples : ∀ x y z : V,
      Bool.xor (Bool.xor (decide (G.Adj x y))
        (decide (G.Adj y z))) (decide (G.Adj z x)) =
      Bool.xor (Bool.xor (decide (G.Adj (f x) (f y)))
        (decide (G.Adj (f y) (f z))))
        (decide (G.Adj (f z) (f x)))) :
    ∃ (h : V → Bool),
      EPPAIII.IsGraphAutomorphism (taylorPairGraph G)
        (taylorSwitchLift f h) ∧
      (∀ b : Bool, ∀ x : V,
        (taylorSwitchLift f h (b,x)).2 = f x) := by
  have hEdgeSym : ∀ x y : V,
      decide (G.Adj x y) = decide (G.Adj y x) := by
    intro x y
    classical
    by_cases hxy : G.Adj x y
    · have hyx := (G.adj_comm x y).mp hxy
      simp [hxy,hyx]
    · have hyx : ¬ G.Adj y x :=
        fun h => hxy ((G.adj_comm x y).mpr h)
      simp [hxy,hyx]
  obtain ⟨h,hDelta⟩ :=
    xor_potential_of_triple_parity
      (fun x y => decide (G.Adj x y)) hEdgeSym f hTriples
  exact ⟨h,taylorSwitchLift_graphAut G f h hDelta,
    fun _ _ => rfl⟩

end EPPAIII.TwoGraphs
