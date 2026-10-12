import EPPAIII.CliqueCovers.Claim39Arithmetic

/-!
# The binomial obstruction in the zero-partial profile classification

In the final no-partial case of Lemma 3.7, a whole outside twin
class meets precisely r of the s selected cliques completely.
Permuting the selected clique indices produces all subsets of
size r. There are only s outside twin classes.

The group-theoretic implication choose(s,r) ≤ s is handled in a
separate orbit lemma; this file formalizes the elementary but
unrestricted arithmetic consequence:

  r ∈ {0,1,s-1,s}.

This uses the earlier proved strict inequality
choose(s,r)>s for 2≤r≤s-2 and has no finite search bound.
-/

namespace EPPAIII.CliqueCovers

/-- An entry of a binomial row no larger than the row index
can occur only at the two ends or their immediate neighbours. -/
theorem choose_le_row_index_extreme (s r : ℕ)
    (hr : r ≤ s)
    (hBound : Nat.choose s r ≤ s) :
    r = 0 ∨ r = 1 ∨ r + 1 = s ∨ r = s := by
  by_contra hNo
  have hNot0 : r ≠ 0 := by
    intro h
    exact hNo (Or.inl h)
  have hNot1 : r ≠ 1 := by
    intro h
    exact hNo (Or.inr (Or.inl h))
  have hNotPrev : r + 1 ≠ s := by
    intro h
    exact hNo (Or.inr (Or.inr (Or.inl h)))
  have hNotLast : r ≠ s := by
    intro h
    exact hNo (Or.inr (Or.inr (Or.inr h)))
  have hr2 : 2 ≤ r := by omega
  have hInterior : r + 2 ≤ s := by omega
  have hStrict := choose_gt_self_interior s r hr2 hInterior
  omega

/-- For a nonempty proper index set, the only possibilities
under the orbit budget are a singleton or a co-singleton. -/
theorem nontrivial_choose_le_row_index (s r : ℕ)
    (hr : 0 < r) (hrs : r < s)
    (hBound : Nat.choose s r ≤ s) :
    r = 1 ∨ r + 1 = s := by
  obtain h0 | h1 | hPrev | hLast :=
    choose_le_row_index_extreme s r hrs.le hBound
  · omega
  · exact Or.inl h1
  · exact Or.inr hPrev
  · omega

end EPPAIII.CliqueCovers
