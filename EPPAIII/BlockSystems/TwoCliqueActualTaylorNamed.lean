import EPPAIII.BlockSystems.TwoCliqueTaylorNamed
import EPPAIII.DoubleCover.UniformPattern

/-!
# Actual Taylor pair pattern identifies its named two-clique host

The structural theorem for unequal selected clique sizes produces
a fixed induced bottom copy, the actual Taylor four-bit pattern
between distinct fibres, and uniform optional mate edges.

Those three properties determine the *whole* graph, not merely the
cross relation. This file proves that identification for arbitrary
vertex types and arbitrary Boolean two-clique partitions.

This closes the source-facing graph-name inference in Lemma 6.6,
conditional only on the exact output of the already validated
actual-host Taylor theorem.
-/

namespace EPPAIII.BlockSystems

/-- A real double carrying a two-clique base, the exact Taylor
pair pattern, and uniform mate edges is the canonical double
of two complete graphs with optional perfect matching. -/
theorem twoClique_actual_taylor_is_matched
    {V : Type*} (c : V → Bool)
    (H : SimpleGraph (Bool × V)) (mate : Bool)
    (hBottom : ∀ x y : V,
      H.Adj (false,x) (false,y) ↔
        (twoCliqueGraph c).Adj x y)
    (hPattern : DoubleCover.RepresentsPairPattern
      (twoCliqueGraph c) H DoubleCover.taylor)
    (hMate : ∀ x : V,
      H.Adj (false,x) (true,x) ↔ mate = true) :
    H = twoCliqueMatchedGraph c mate := by
  classical
  have hTop (x y : V) :
      H.Adj (true,x) (true,y) ↔
        (x ≠ y ∧ c x = c y) := by
    by_cases hxy : x = y
    · subst y
      simp
    · by_cases hc : c x = c y
      · have hG : (twoCliqueGraph c).Adj x y := ⟨hxy,hc⟩
        have h : H.Adj (true,x) (true,y) :=
          (hPattern.1 x y hxy hG).2.2.mpr (by decide)
        simp [hxy,hc,h]
      · have hG : ¬ (twoCliqueGraph c).Adj x y := by
          intro h
          exact hc h.2
        have h : ¬ H.Adj (true,x) (true,y) := by
          have hh := (hPattern.2 x y hxy hG).2.2
          simpa [DoubleCover.taylor] using hh
        simp [hxy,hc,h]
  have hCross (x y : V) :
      H.Adj (false,x) (true,y) ↔
        ((x ≠ y ∧ c x ≠ c y) ∨
          (mate = true ∧ x = y)) := by
    by_cases hxy : x = y
    · subst y
      simpa using hMate x
    · by_cases hc : c x = c y
      · have hG : (twoCliqueGraph c).Adj x y := ⟨hxy,hc⟩
        have h : ¬ H.Adj (false,x) (true,y) := by
          have hh := (hPattern.1 x y hxy hG).1
          simpa [DoubleCover.taylor] using hh
        simp [hxy,hc,h]
      · have hG : ¬ (twoCliqueGraph c).Adj x y := by
          intro h
          exact hc h.2
        have h : H.Adj (false,x) (true,y) :=
          (hPattern.2 x y hxy hG).1.mpr (by decide)
        simp [hxy,hc,h]
  apply twoCliqueTaylorGraph_eq_matched c mate H
  intro u v
  rcases u with ⟨a,x⟩
  rcases v with ⟨b,y⟩
  cases a <;> cases b
  · simpa [twoCliqueTaylorRel, twoCliqueGraph] using hBottom x y
  · simpa [twoCliqueTaylorRel] using hCross x y
  · have h := (H.adj_comm (true,x) (false,y)).trans (hCross y x)
    simpa [twoCliqueTaylorRel, eq_comm, ne_comm] using h
  · simpa [twoCliqueTaylorRel] using hTop x y

end EPPAIII.BlockSystems
