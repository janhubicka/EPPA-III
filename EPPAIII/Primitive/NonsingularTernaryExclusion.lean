import EPPAIII.Primitive.NonsingularTernaryProfiles

/-! # Nonsingular even-dimensional ternary constituents -/

namespace EPPAIII.Primitive

open SimpleGraph

attribute [local instance] Classical.propDecidable

private def ternaryDegreeDifference (a : ℕ) : ℕ :=
  3 * (2 * a + 1) * (2 * a + 1)

/-- The two codegrees of the local orthogonality graph are equal. -/
def evenTernaryLocalCodegree (a : ℕ) (plus : Bool) : ℕ :=
  (2 * a + 1) * (a + if plus then 1 else 0)

/-- The published host SRG parameters suffice to exclude all four forms for
both rooted constituents. -/
theorem evenTernary_constituents_exclude_forms_of_host {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {a : ℕ} (ha : 1 ≤ a) (plus : Bool)
    (hHost : let p := evenTernaryParameters a plus
      H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon)
    (root : V) (side : Bool) :
    let G := constituentGraph H root side
    (∀ s t, IsEmpty (G ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (G ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (G ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) := by
  cases side
  · exact evenTernary_local_excludes_forms H ha plus hHost root
  · let p := evenTernaryParameters a plus
    let d := ternaryDegreeDifference a
    have hBound : d ≤ p.degree := by
      cases plus <;> simp [p, d, ternaryDegreeDifference, evenTernaryParameters] <;>
        nlinarith
    have h := constituentGraph_profile H p hHost root true
    change HasRegularProfile _ (p.order - p.degree - 1, p.degree - p.nonadjacentCommon) at h
    have hOrder : p.order - p.degree - 1 = 3 * d - 1 := by
      simp [p, d, evenTernaryParameters, ternaryDegreeDifference]
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

set_option linter.unusedVariables false in
/-- The earlier interface with an explicit local SRG hypothesis. -/
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
    (∀ s t X Y, IsEmpty (G ≃g (coverGraph s t X Y)ᶜ)) :=
  evenTernary_constituents_exclude_forms_of_host H ha plus hHost root side

end EPPAIII.Primitive
