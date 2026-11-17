import Lean.Elab.Tactic.Omega

/-!
# A finite order bound for the small-subconstituent screen

The signatures below are the distinct (order, regular degree) pairs
in R17's small-subconstituent table. This file proves only the bound
needed to search the external catalogue, from the SRG parameter
equation and the positivity of the common-neighbor count on nonedges.
It does not infer graph isomorphism from an SRG parameter tuple.
-/

namespace EPPAIII.Primitive

/-- The local order and degree pairs for the candidates listed in the
manuscript table, in the displayed orientations. -/
def smallConstituentProfiles : List (Nat × Nat) :=
  [(5, 2), (9, 4), (10, 2), (18, 4), (10, 4), (18, 8), (8, 3),
    (10, 3), (18, 5), (12, 5), (16, 6), (16, 5), (20, 9), (27, 16)]

/-- The same candidates in both orientations. A nonlocal occurrence
in the original host can be treated as a local occurrence in its
complement, where the local graph is complemented as well. -/
def smallConstituentProfilesWithComplements : List (Nat × Nat) :=
  smallConstituentProfiles ++
    smallConstituentProfiles.map (fun (k, l) => (k, k - l - 1))

/-- The standard parameter equation bounds the order once the order
and regular degree of a first subconstituent are known. -/
theorem srg_order_le_of_local_profile {n k l m : Nat}
    (hParams : k * (k - l - 1) = (n - k - 1) * m) (hM : 0 < m) :
    n ≤ k + 1 + k * (k - l - 1) := by
  have h := Nat.le_mul_of_pos_right (n - k - 1) hM
  rw [← hParams] at h
  omega

/-- All the table's candidate local profiles, allowing either
complementary orientation, bound the order by 460. This bound is on
parameters and does not require the graph's EPPA property. -/
theorem smallConstituent_host_order_le_460 {n k l m : Nat}
    (hProfile : (k, l) ∈ smallConstituentProfilesWithComplements)
    (hParams : k * (k - l - 1) = (n - k - 1) * m) (hM : 0 < m) :
    n ≤ 460 := by
  have hAll : smallConstituentProfilesWithComplements.all
      (fun (k, l) => decide (k + 1 + k * (k - l - 1) ≤ 460)) = true := by
    decide
  have hBound : k + 1 + k * (k - l - 1) ≤ 460 :=
    of_decide_eq_true (List.all_eq_true.mp hAll (k, l) hProfile)
  exact Nat.le_trans (srg_order_le_of_local_profile hParams hM) hBound

end EPPAIII.Primitive
