import EPPAIII.TwoGraphs.OneForAll

namespace EPPAIII.TwoGraphs

/-- Every ordered pair of distinct vertices of a homogeneous two-graph belongs
to the same orbit. A two-point restriction contains no odd triple. -/
theorem two_graph_homogeneous_ordered_pairs {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hHom : IsHomogeneousTwoGraph G)
    (a b x y : V) (hab : a ≠ b) (hxy : x ≠ y) :
    ∃ p : Equiv.Perm V, IsTwoGraphAutomorphism G p ∧ p a = x ∧ p b = y := by
  classical
  let q := Equiv.swap a x
  let p := q.trans (Equiv.swap (q b) y)
  have hqa : q a = x := Equiv.swap_apply_left a x
  have hqbx : q b ≠ x := by
    rw [← hqa]
    exact q.injective.ne hab.symm
  have hpa : p a = x := by
    change Equiv.swap (q b) y (q a) = x
    rw [hqa, Equiv.swap_apply_of_ne_of_ne hqbx.symm hxy]
  have hpb : p b = y := Equiv.swap_apply_left (q b) y
  have hPartial : IsPartialTwoGraphAutomorphism G {a, b} p := by
    intro u hu v hv w hw
    have hRepeated : u = v ∨ v = w ∨ w = u := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        rcases hw with rfl | rfl <;> simp
    have hImageRepeated : p u = p v ∨ p v = p w ∨ p w = p u :=
      hRepeated.imp (congrArg p) (Or.imp (congrArg p) (congrArg p))
    exact iff_of_false (oddBaseTriple_repeated_false G u v w hRepeated)
      (oddBaseTriple_repeated_false G (p u) (p v) (p w) hImageRepeated)
  obtain ⟨σ, hσ, hExtend⟩ := hHom {a, b} p hPartial
  exact ⟨σ, hσ, (hExtend a (by simp)).trans hpa, (hExtend b (by simp)).trans hpb⟩

/-- In a nontrivial homogeneous two-graph every ordered pair of distinct
vertices has an odd extension and an even extension. -/
theorem two_graph_homogeneous_has_third_points {V : Type*}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hHom : IsHomogeneousTwoGraph G)
    (hOdd : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ OddBaseTriple G x y z)
    (hEven : ∃ x y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ¬ OddBaseTriple G x y z)
    (a b : V) (hab : a ≠ b) :
    (∃ c : V, a ≠ c ∧ b ≠ c ∧ OddBaseTriple G a b c) ∧
      (∃ c : V, a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple G a b c) := by
  have transport (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
      ∃ c : V, a ≠ c ∧ b ≠ c ∧ (OddBaseTriple G x y z ↔ OddBaseTriple G a b c) := by
    obtain ⟨p, hp, hpa, hpb⟩ := two_graph_homogeneous_ordered_pairs G hHom x y a b hxy hab
    refine ⟨p z, ?_, ?_, ?_⟩
    · exact hpa ▸ p.injective.ne hxz
    · exact hpb ▸ p.injective.ne hyz
    · simpa only [hpa, hpb] using hp x y z
  obtain ⟨x, y, z, hxy, hxz, hyz, hParity⟩ := hOdd
  obtain ⟨u, v, w, huv, huw, hvw, hNotParity⟩ := hEven
  obtain ⟨c, hac, hbc, hc⟩ := transport x y z hxy hxz hyz
  obtain ⟨d, had, hbd, hd⟩ := transport u v w huv huw hvw
  exact ⟨⟨c, hac, hbc, hc.mp hParity⟩, ⟨d, had, hbd, fun h => hNotParity (hd.mpr h)⟩⟩

end EPPAIII.TwoGraphs
