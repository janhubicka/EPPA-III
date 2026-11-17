import EPPAIII.Primitive.RookCoordinateExtension

/-!
# Two families of EPPA selections in square rook graphs

The three-by-three corner with isolated diagonal points has no
same-direction induced matching. The two-column stripe has no
opposite-direction induced matching.
-/

namespace EPPAIII.Primitive

/-- The three-by-three corner and the remaining diagonal cells. -/
def rookThreeCorner (n : ℕ) : Set (Fin n × Fin n) :=
  {x | (x.1.val < 3 ∧ x.2.val < 3) ∨ (3 ≤ x.1.val ∧ x.1.val = x.2.val)}

/-- All cells in the first two columns of the square rook graph. -/
def rookTwoColumns (n : ℕ) : Set (Fin n × Fin n) :=
  {x | x.2.val < 2}

private theorem corner_edge_inside {n : ℕ} {x y : rookThreeCorner n}
    (h : (rookGraph n).Adj x.val y.val) :
    x.val.1.val < 3 ∧ x.val.2.val < 3 ∧ y.val.1.val < 3 ∧ y.val.2.val < 3 := by
  have hx := x.property
  have hy := y.property
  change (_ ∧ _) ∨ (_ ∧ _) at hx hy
  have hNe : ¬ (x.val.1.val = y.val.1.val ∧ x.val.2.val = y.val.2.val) :=
    fun hEq => h.1 (Prod.ext (Fin.ext hEq.1) (Fin.ext hEq.2))
  have hAxis : x.val.1.val = y.val.1.val ∨ x.val.2.val = y.val.2.val :=
    h.2.imp (congrArg Fin.val) (congrArg Fin.val)
  omega

private theorem matching_cross_ne {n : ℕ} {a b c d : Fin n × Fin n}
    (h : RookInducedMatching a b c d) :
    (a.1.val ≠ c.1.val ∧ a.2.val ≠ c.2.val) ∧
    (a.1.val ≠ d.1.val ∧ a.2.val ≠ d.2.val) ∧
    (b.1.val ≠ c.1.val ∧ b.2.val ≠ c.2.val) ∧
    (b.1.val ≠ d.1.val ∧ b.2.val ≠ d.2.val) := by
  obtain ⟨_, _, hac, had, hbc, hbd, nac, nad, nbc, nbd⟩ := h
  have both {x y : Fin n × Fin n} (hne : x ≠ y) (hn : ¬ (rookGraph n).Adj x y) :
      x.1.val ≠ y.1.val ∧ x.2.val ≠ y.2.val :=
    ⟨fun e => hn ⟨hne, Or.inl (Fin.ext e)⟩, fun e => hn ⟨hne, Or.inr (Fin.ext e)⟩⟩
  exact ⟨both hac nac, both had nad, both hbc nbc, both hbd nbd⟩

/-- The square rook graph witnesses the three-by-three corner together
with any number of isolated remaining diagonal points. -/
theorem rookThreeCorner_eppa (n : ℕ) :
    IsEPPAEmbedding ((rookGraph n).induce (rookThreeCorner n)) (rookGraph n)
      (Function.Embedding.subtype (rookThreeCorner n)) := by
  apply rookGraph_eppa_of_matchingDirection _ False
  intro a b c d h
  have hab := corner_edge_inside h.1
  have hcd := corner_edge_inside h.2.1
  obtain ⟨⟨hacR, hacC⟩, ⟨hadR, hadC⟩, ⟨hbcR, hbcC⟩, ⟨hbdR, hbdC⟩⟩ :=
    matching_cross_ne h
  refine ⟨fun hDir => ?_, False.elim⟩
  by_cases hRow : a.val.1 = b.val.1
  · have hRow' := hDir.mp hRow
    have h1 : a.val.2.val ≠ b.val.2.val :=
      fun e => h.1.1 (Prod.ext hRow (Fin.ext e))
    have h2 : c.val.2.val ≠ d.val.2.val :=
      fun e => h.2.1.1 (Prod.ext hRow' (Fin.ext e))
    omega
  · have hRow' : c.val.1 ≠ d.val.1 := fun e => hRow (hDir.mpr e)
    have h1 : a.val.1.val ≠ b.val.1.val := fun e => hRow (Fin.ext e)
    have h2 : c.val.1.val ≠ d.val.1.val := fun e => hRow' (Fin.ext e)
    omega

/-- The square rook graph witnesses the two-column stripe. -/
theorem rookTwoColumns_eppa (n : ℕ) :
    IsEPPAEmbedding ((rookGraph n).induce (rookTwoColumns n)) (rookGraph n)
      (Function.Embedding.subtype (rookTwoColumns n)) := by
  apply rookGraph_eppa_of_matchingDirection _ True
  intro a b c d h
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨⟨_, hacC⟩, ⟨_, hadC⟩, ⟨_, hbcC⟩, _⟩ := matching_cross_ne h
  have ha : a.val.2.val < 2 := a.property
  have hb : b.val.2.val < 2 := b.property
  have hc : c.val.2.val < 2 := c.property
  have hd : d.val.2.val < 2 := d.property
  constructor
  · intro hRow
    have hNe : a.val.2.val ≠ b.val.2.val :=
      fun e => h.1.1 (Prod.ext hRow (Fin.ext e))
    exfalso
    omega
  · intro hRow
    have hNe : c.val.2.val ≠ d.val.2.val :=
      fun e => h.2.1.1 (Prod.ext hRow (Fin.ext e))
    exfalso
    omega

end EPPAIII.Primitive
