import EPPAIII.BlockSystems.TransitivePartition

/-!
# Canonical paired-fibre coordinates for an invariant two-point block system

Given an induced embedding e : V ↪ W meeting each block in one point,
with exactly two host vertices per block and |W| = 2|V|,
there is an equivalence Bool × V ≃ W sending (false,x) to e x
and (true,x) to its unique other vertex in the same block.

The existence and bijectivity of this equivalence are proved rather
than assumed. It will allow the generic-block formalization of
Claim 3.4 to feed into the Taylor-double result of CompleteTaylor.
-/

namespace EPPAIII.BlockSystems

/-- A two-element block containing a chosen point also contains
a different point. -/
private theorem two_fibre_has_other {V W B : Type*}
    [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B) (x : V)
    (hTwo :
      ((Finset.univ : Finset W).filter
        (fun w => block w = block (e x))).card = 2) :
    ∃ w : W, block w = block (e x) ∧ w ≠ e x := by
  classical
  let s : Finset W :=
    (Finset.univ : Finset W).filter
      (fun w => block w = block (e x))
  have hx : e x ∈ s := by simp [s]
  by_contra hNo
  have hSubset : s ⊆ {e x} := by
    intro w hw
    have hwBlock : block w = block (e x) :=
      (Finset.mem_filter.mp hw).2
    have hEq : w = e x := by
      by_contra hn
      exact hNo ⟨w, hwBlock, hn⟩
    simpa [hEq]
  have hSupset : ({e x} : Finset W) ⊆ s := by
    simpa using hx
  have hEq : s = {e x} :=
    Finset.Subset.antisymm hSubset hSupset
  have hOne : s.card = 1 := by
    rw [hEq]
    simp
  have hTwo' : s.card = 2 := hTwo
  omega

/-- **Canonical coordinates for paired invariant blocks.**

The embedding e occupies the bottom of each pair, and the other
half is constructed by choosing the second point of each two-element
block. Block injectivity and cardinal equality make this choice a
bijection with the whole host. -/
theorem exists_canonical_pair_equiv {V W B : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq B]
    (e : V ↪ W) (block : W → B)
    (hInjective : Function.Injective (fun x : V => block (e x)))
    (hTwo : ∀ b : B,
      ((Finset.univ : Finset W).filter
        (fun w => block w = b)).card = 2)
    (hHostSize : Fintype.card W = 2 * Fintype.card V) :
    ∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      (∀ (b : Bool) (x : V),
        block (φ (b,x)) = block (e x)) := by
  classical
  let mate : V → W := fun x =>
    Classical.choose
      (two_fibre_has_other e block x (hTwo (block (e x))))
  have hm (x : V) :
      block (mate x) = block (e x) ∧ mate x ≠ e x := by
    exact Classical.choose_spec
      (two_fibre_has_other e block x (hTwo (block (e x))))
  let f : Bool × V → W :=
    fun bx => if bx.1 then mate bx.2 else e bx.2
  have hBlock (b : Bool) (x : V) :
      block (f (b,x)) = block (e x) := by
    cases b
    · rfl
    · exact (hm x).1
  have hInj : Function.Injective f := by
    rintro ⟨b,x⟩ ⟨c,y⟩ hf
    have hxy : x = y := hInjective (by
      calc
        block (e x) = block (f (b,x)) := (hBlock b x).symm
        _ = block (f (c,y)) := congrArg block hf
        _ = block (e y) := hBlock c y)
    subst y
    cases b <;> cases c
    · rfl
    · have he : e x = mate x := by simpa [f] using hf
      exact False.elim ((hm x).2 he.symm)
    · have he : mate x = e x := by simpa [f] using hf
      exact False.elim ((hm x).2 he)
    · rfl
  have hCard : Fintype.card (Bool × V) = Fintype.card W := by
    calc
      Fintype.card (Bool × V) = 2 * Fintype.card V := by
        simp [Fintype.card_prod]
      _ = Fintype.card W := hHostSize.symm
  have hSurj : Function.Surjective f := by
    intro w
    let im : Finset W :=
      (Finset.univ : Finset (Bool × V)).image f
    have hImCard : im.card = Fintype.card (Bool × V) := by
      simpa [im] using
        (Finset.card_image_of_injective
          (Finset.univ : Finset (Bool × V)) hInj)
    have hBound : (Finset.univ : Finset W).card ≤ im.card := by
      simpa [hImCard, hCard]
    have hFull : im = (Finset.univ : Finset W) :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hBound
    have hw : w ∈ im := by rw [hFull]; simp
    obtain ⟨bx, _, hb⟩ := Finset.mem_image.mp hw
    exact ⟨bx, hb⟩
  let φ : Bool × V ≃ W :=
    Equiv.ofBijective f ⟨hInj, hSurj⟩
  refine ⟨φ, ?_, ?_⟩
  · intro x
    rfl
  · intro b x
    exact hBlock b x

end EPPAIII.BlockSystems
