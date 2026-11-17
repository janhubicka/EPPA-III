import EPPAIII.Primitive.NonsingularTernaryProfiles
import EPPAIII.Primitive.StronglyRegularCovers

/-! # Nonsingular even-dimensional ternary constituents -/

namespace EPPAIII.Primitive

open SimpleGraph

attribute [local instance] Classical.propDecidable

private def ternaryDegreeDifference (a : ℕ) : ℕ :=
  3 * (2 * a + 1) * (2 * a + 1)

/-- The published parameters of `NO^ε_(2m)(3)`, written using the integer
`a = (3^(m-2) - 1)/2`. The Boolean selects the positive sign. -/
def evenTernaryParameters (a : ℕ) (plus : Bool) : SRGParameters :=
  let r := 2 * a + 1
  let k := 3 * r * (3 * a + if plus then 1 else 2)
  let l := r * (3 * a + if plus then 2 else 1)
  let d := ternaryDegreeDifference a
  ⟨k + 3 * d, k, l, k - d⟩

/-- The two codegrees of the local orthogonality graph are equal. -/
def evenTernaryLocalCodegree (a : ℕ) (plus : Bool) : ℕ :=
  (2 * a + 1) * (a + if plus then 1 else 0)

/-- Given the published host and local SRG parameter formulas, each
rooted constituent is forbidden by the four-shape reduction. -/
theorem evenTernary_constituents_exclude_forms {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {a : ℕ} (ha : 1 ≤ a) (plus : Bool)
    (hHost : let p := evenTernaryParameters a plus
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (hLocal : ∀ root, let p := evenTernaryParameters a plus
      let μ := evenTernaryLocalCodegree a plus
      (constituentGraph H root false).IsSRGWith p.degree p.adjacentCommon μ μ)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  cases side
  · have h := hLocal root
    apply srg_positive_codegrees_exclude_forms _ h
    all_goals cases plus <;>
      simp [evenTernaryParameters, evenTernaryLocalCodegree] <;>
      first | omega | (apply lt_of_le_of_lt (Nat.sub_le _ _); nlinarith) | nlinarith
  · let p := evenTernaryParameters a plus
    let d := ternaryDegreeDifference a
    have hBound : d ≤ p.degree := by
      cases plus <;> simp [p, d, ternaryDegreeDifference, evenTernaryParameters] <;>
        nlinarith
    have h := constituentGraph_profile H p hHost root true
    change HasRegularProfile _ (p.order - p.degree - 1, p.degree - p.nonadjacentCommon) at h
    have hOrder : p.order - p.degree - 1 = 3 * d - 1 := by
      simp [p, d, evenTernaryParameters]
    have hDegree : p.degree - p.nonadjacentCommon = d := by
      change p.degree - (p.degree - d) = d
      omega
    rw [hOrder, hDegree] at h
    apply tripled_odd_degree_excludes_forms _ _ h
    · dsimp [d, ternaryDegreeDifference]
      nlinarith
    · dsimp [d, ternaryDegreeDifference]
      have hR : Odd (2 * a + 1) := Nat.odd_iff.mpr (by omega)
      exact Nat.odd_iff.mp (((by decide : Odd (3 : ℕ)).mul hR).mul hR)

end EPPAIII.Primitive
