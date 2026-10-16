import Mathlib

/-!
# Direct Seidel switching identity for two-clique graphs

This proves the switching-class assertion of current Lemma 6.6:
a Boolean vertex colouring yields a disjoint union of two cliques.
Every other partition into two cliques, including the trivial one,
is obtained by switching across the set of changed colours.
No external switching classification is used.
-/

namespace EPPAIII.BlockSystems

/-- The disjoint union of the two colour classes, allowing empties. -/
def twoCliqueGraph {V : Type*} (color : V → Bool) : SimpleGraph V where
  Adj u v := u ≠ v ∧ color u = color v
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Seidel switching toggles edges across a Boolean mask. -/
def seidelSwitchGraph {V : Type*}
    (H : SimpleGraph V) (mask : V → Bool) : SimpleGraph V where
  Adj u v := u ≠ v ∧
    (if mask u = mask v then H.Adj u v else ¬ H.Adj u v)
  symm := by
    constructor
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    by_cases hm : mask u = mask v
    · have hm' : mask v = mask u := hm.symm
      have hu : H.Adj u v := by simpa only [if_pos hm] using h.2
      have hv : H.Adj v u := hu.symm
      simpa only [if_pos hm'] using hv
    · have hm' : mask v ≠ mask u := fun h' => hm h'.symm
      have hu : ¬ H.Adj u v := by simpa only [if_neg hm] using h.2
      have hv : ¬ H.Adj v u := fun h' => hu h'.symm
      simpa only [if_neg hm'] using hv
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- Any two partitions into two cliques are Seidel switching equivalent. -/
theorem twoCliqueGraph_switch_to_any_twoClique {V : Type*}
    (c d : V → Bool) :
    seidelSwitchGraph (twoCliqueGraph c)
      (fun v => Bool.xor (c v) (d v)) = twoCliqueGraph d := by
  classical
  apply SimpleGraph.ext
  funext u v
  apply propext
  by_cases hEq : u = v
  · subst v
    simp [seidelSwitchGraph,twoCliqueGraph]
  · cases hcu : c u <;> cases hcv : c v <;>
      cases hdu : d u <;> cases hdv : d v <;>
      simp [seidelSwitchGraph,twoCliqueGraph,hEq,
        hcu,hcv,hdu,hdv,Bool.xor]

/-- A constant colouring gives the complete graph. -/
theorem twoCliqueGraph_constant_eq_complete {V : Type*} :
    twoCliqueGraph (fun _ : V => false) = (⊤ : SimpleGraph V) := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  simp [twoCliqueGraph]

/-- The complete graph belongs to the switching class of any
two-clique partition. -/
theorem twoCliqueGraph_switch_to_complete {V : Type*}
    (c : V → Bool) :
    seidelSwitchGraph (twoCliqueGraph c) c = (⊤ : SimpleGraph V) := by
  have h := twoCliqueGraph_switch_to_any_twoClique
    c (fun _ : V => false)
  simpa [Bool.xor, twoCliqueGraph_constant_eq_complete] using h

end EPPAIII.BlockSystems
