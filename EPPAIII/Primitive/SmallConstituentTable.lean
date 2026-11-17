import EPPAIII.Primitive.SmallConstituentBound

/-!
# Finite parameter screen for small primitive rank-three hosts

The source is Brouwer and Van Maldeghem, *Strongly Regular Graphs*,
Table 11.8, author preprint pages 365–367 (PDF pages 381–383).
The list runs through the last row of order at most 460. Repeated
parameter tuples are retained because they come from distinct rows.
The first row is the 5-cycle and has adjacent codegree 0, whereas
the preprint prints 1. The values 12 for the halved folded 8-cube's
nonadjacent codegree and 353 for the order of the Paley graph with
valency 176 agree with the current author PDF.

The theorem checks all rows in both complementary orientations.
It is purely numerical. The rank-three classification, named-model
identifications, and actual induced subconstituent identities are
separate graph-theoretic inputs.
-/

namespace EPPAIII.Primitive

structure SRGParameters where
  order : Nat
  degree : Nat
  adjacentCommon : Nat
  nonadjacentCommon : Nat
  deriving DecidableEq

namespace SRGParameters

/-- Use the same natural-number subtraction as mathlib's `IsSRGWith.compl`. -/
def compl (p : SRGParameters) : SRGParameters :=
  ⟨p.order, p.order - p.degree - 1,
    p.order - (2 * p.degree - p.nonadjacentCommon) - 2,
    p.order - (2 * p.degree - p.adjacentCommon)⟩

/-- The order and regular degree of a rooted constituent.
Here `false` means the first constituent and `true` the second. -/
def constituentProfile (p : SRGParameters) : Bool → Nat × Nat
  | false => (p.degree, p.adjacentCommon)
  | true => (p.order - p.degree - 1, p.degree - p.nonadjacentCommon)

/-- The ordinary parameter equation. -/
def ParameterEquation (p : SRGParameters) : Prop :=
  p.degree * (p.degree - p.adjacentCommon - 1) =
    (p.order - p.degree - 1) * p.nonadjacentCommon

instance (p : SRGParameters) : Decidable p.ParameterEquation :=
  inferInstanceAs (Decidable (_ = _))

end SRGParameters

/-- The numerical columns of all 168 source rows with order at most 460. -/
def smallRankThreeTable : List SRGParameters :=
  [⟨5, 2, 0, 1⟩, ⟨9, 4, 1, 2⟩, ⟨10, 3, 0, 1⟩, ⟨13, 6, 2, 3⟩,
    ⟨15, 6, 1, 3⟩, ⟨16, 5, 0, 2⟩, ⟨16, 6, 2, 2⟩, ⟨17, 8, 3, 4⟩,
    ⟨21, 10, 5, 4⟩, ⟨25, 8, 3, 2⟩, ⟨25, 12, 5, 6⟩, ⟨27, 10, 1, 5⟩,
    ⟨28, 12, 6, 4⟩, ⟨29, 14, 6, 7⟩, ⟨35, 16, 6, 8⟩, ⟨36, 10, 4, 2⟩,
    ⟨36, 14, 4, 6⟩, ⟨36, 14, 7, 4⟩, ⟨36, 15, 6, 6⟩, ⟨37, 18, 8, 9⟩,
    ⟨40, 12, 2, 4⟩, ⟨40, 12, 2, 4⟩, ⟨41, 20, 9, 10⟩, ⟨45, 12, 3, 3⟩,
    ⟨45, 16, 8, 4⟩, ⟨49, 12, 5, 2⟩, ⟨49, 24, 11, 12⟩, ⟨49, 24, 11, 12⟩,
    ⟨50, 7, 0, 1⟩, ⟨53, 26, 12, 13⟩, ⟨55, 18, 9, 4⟩, ⟨56, 10, 0, 2⟩,
    ⟨61, 30, 14, 15⟩, ⟨63, 30, 13, 15⟩, ⟨64, 14, 6, 2⟩, ⟨64, 18, 2, 6⟩,
    ⟨64, 21, 8, 6⟩, ⟨64, 27, 10, 12⟩, ⟨64, 28, 12, 12⟩, ⟨66, 20, 10, 4⟩,
    ⟨73, 36, 17, 18⟩, ⟨77, 16, 0, 4⟩, ⟨78, 22, 11, 4⟩, ⟨81, 16, 7, 2⟩,
    ⟨81, 20, 1, 6⟩, ⟨81, 32, 13, 12⟩, ⟨81, 40, 19, 20⟩, ⟨81, 40, 19, 20⟩,
    ⟨85, 20, 3, 5⟩, ⟨89, 44, 21, 22⟩, ⟨91, 24, 12, 4⟩, ⟨97, 48, 23, 24⟩,
    ⟨100, 18, 8, 2⟩, ⟨100, 22, 0, 6⟩, ⟨100, 36, 14, 12⟩, ⟨101, 50, 24, 25⟩,
    ⟨105, 26, 13, 4⟩, ⟨109, 54, 26, 27⟩, ⟨112, 30, 2, 10⟩, ⟨113, 56, 27, 28⟩,
    ⟨117, 36, 15, 9⟩, ⟨119, 54, 21, 27⟩, ⟨120, 28, 14, 4⟩, ⟨120, 51, 18, 24⟩,
    ⟨120, 56, 28, 24⟩, ⟨121, 20, 9, 2⟩, ⟨121, 40, 15, 12⟩, ⟨121, 60, 29, 30⟩,
    ⟨121, 60, 29, 30⟩, ⟨125, 62, 30, 31⟩, ⟨126, 25, 8, 4⟩, ⟨126, 45, 12, 18⟩,
    ⟨130, 48, 20, 16⟩, ⟨135, 64, 28, 32⟩, ⟨136, 30, 15, 4⟩, ⟨136, 60, 24, 28⟩,
    ⟨136, 63, 30, 28⟩, ⟨137, 68, 33, 34⟩, ⟨144, 22, 10, 2⟩, ⟨149, 74, 36, 37⟩,
    ⟨153, 32, 16, 4⟩, ⟨155, 42, 17, 9⟩, ⟨156, 30, 4, 6⟩, ⟨156, 30, 4, 6⟩,
    ⟨157, 78, 38, 39⟩, ⟨162, 56, 10, 24⟩, ⟨165, 36, 3, 9⟩, ⟨169, 24, 11, 2⟩,
    ⟨169, 72, 31, 30⟩, ⟨169, 84, 41, 42⟩, ⟨171, 34, 17, 4⟩, ⟨173, 86, 42, 43⟩,
    ⟨176, 40, 12, 8⟩, ⟨176, 70, 18, 34⟩, ⟨181, 90, 44, 45⟩, ⟨190, 36, 18, 4⟩,
    ⟨193, 96, 47, 48⟩, ⟨196, 26, 12, 2⟩, ⟨197, 98, 48, 49⟩, ⟨210, 38, 19, 4⟩,
    ⟨225, 28, 13, 2⟩, ⟨229, 114, 56, 57⟩, ⟨231, 40, 20, 4⟩, ⟨233, 116, 57, 58⟩,
    ⟨241, 120, 59, 60⟩, ⟨243, 22, 1, 2⟩, ⟨243, 110, 37, 60⟩, ⟨253, 42, 21, 4⟩,
    ⟨253, 112, 36, 60⟩, ⟨255, 126, 61, 63⟩, ⟨256, 30, 14, 2⟩, ⟨256, 45, 16, 6⟩,
    ⟨256, 45, 16, 6⟩, ⟨256, 51, 2, 12⟩, ⟨256, 75, 26, 20⟩, ⟨256, 85, 24, 30⟩,
    ⟨256, 102, 38, 42⟩, ⟨256, 119, 54, 56⟩, ⟨256, 120, 56, 56⟩, ⟨257, 128, 63, 64⟩,
    ⟨269, 134, 66, 67⟩, ⟨275, 112, 30, 56⟩, ⟨276, 44, 22, 4⟩, ⟨277, 138, 68, 69⟩,
    ⟨280, 36, 8, 4⟩, ⟨281, 140, 69, 70⟩, ⟨289, 32, 15, 2⟩, ⟨289, 96, 35, 30⟩,
    ⟨289, 96, 35, 30⟩, ⟨289, 144, 71, 72⟩, ⟨293, 146, 72, 73⟩, ⟨297, 40, 7, 5⟩,
    ⟨300, 46, 23, 4⟩, ⟨313, 156, 77, 78⟩, ⟨317, 158, 78, 79⟩, ⟨324, 34, 16, 2⟩,
    ⟨325, 48, 24, 4⟩, ⟨325, 68, 3, 17⟩, ⟨337, 168, 83, 84⟩, ⟨349, 174, 86, 87⟩,
    ⟨351, 50, 25, 4⟩, ⟨351, 126, 45, 45⟩, ⟨353, 176, 87, 88⟩, ⟨357, 100, 35, 25⟩,
    ⟨361, 36, 17, 2⟩, ⟨361, 144, 59, 56⟩, ⟨361, 180, 89, 90⟩, ⟨361, 180, 89, 90⟩,
    ⟨364, 120, 38, 40⟩, ⟨364, 120, 38, 40⟩, ⟨373, 186, 92, 93⟩, ⟨378, 52, 26, 4⟩,
    ⟨378, 117, 36, 36⟩, ⟨389, 194, 96, 97⟩, ⟨397, 198, 98, 99⟩, ⟨400, 38, 18, 2⟩,
    ⟨400, 56, 6, 8⟩, ⟨400, 56, 6, 8⟩, ⟨401, 200, 99, 100⟩, ⟨406, 54, 27, 4⟩,
    ⟨409, 204, 101, 102⟩, ⟨416, 100, 36, 20⟩, ⟨421, 210, 104, 105⟩, ⟨433, 216, 107, 108⟩,
    ⟨435, 56, 28, 4⟩, ⟨441, 40, 19, 2⟩, ⟨449, 224, 111, 112⟩, ⟨457, 228, 113, 114⟩]

/-- Include the other orientation even when it has the same degree. -/
def orientedSmallRankThreeTable : List SRGParameters :=
  smallRankThreeTable.flatMap (fun p => [p, p.compl])

/-- The listed orientation-specific matches in R17. Each repeated
order-degree profile is checked once and can represent several
candidate subconstituent models. -/
def smallConstituentHits : List (SRGParameters × Bool) :=
  [(⟨15, 6, 1, 3⟩, true), (⟨16, 5, 0, 2⟩, true),
    (⟨16, 6, 2, 2⟩, true), (⟨16, 9, 4, 6⟩, false),
    (⟨17, 8, 3, 4⟩, false), (⟨21, 10, 3, 6⟩, false),
    (⟨21, 10, 3, 6⟩, true), (⟨25, 8, 3, 2⟩, false),
    (⟨25, 8, 3, 2⟩, true), (⟨25, 12, 5, 6⟩, false),
    (⟨27, 10, 1, 5⟩, true), (⟨28, 15, 6, 10⟩, true),
    (⟨35, 16, 6, 8⟩, false), (⟨35, 16, 6, 8⟩, true),
    (⟨36, 10, 4, 2⟩, false), (⟨36, 15, 6, 6⟩, true),
    (⟨37, 18, 8, 9⟩, false), (⟨41, 20, 9, 10⟩, false),
    (⟨49, 12, 5, 2⟩, false), (⟨55, 36, 21, 28⟩, true),
    (⟨64, 36, 20, 20⟩, true), (⟨66, 45, 28, 36⟩, true),
    (⟨100, 18, 8, 2⟩, false), (⟨121, 20, 9, 2⟩, false)]

/-- Independently compute all matches from the source rows. -/
def calculatedSmallConstituentHits : List (SRGParameters × Bool) :=
  ((orientedSmallRankThreeTable.flatMap fun p => [(p, false), (p, true)]).filter
    fun (p, side) => decide (p.constituentProfile side ∈ smallConstituentProfiles)).eraseDups

set_option maxRecDepth 8192 in
theorem smallRankThreeTable_size : smallRankThreeTable.length = 168 := by decide

set_option maxRecDepth 2048 in
theorem smallRankThreeTable_valid :
    smallRankThreeTable.all (fun p => decide
      (p.order ≤ 460 ∧ p.degree ≤ p.order - p.degree - 1 ∧ p.ParameterEquation)) = true := by
  decide

set_option maxRecDepth 8192 in
theorem calculatedSmallConstituentHits_eq :
    calculatedSmallConstituentHits = smallConstituentHits := by decide

theorem smallConstituentHits_complete {p : SRGParameters} {side : Bool}
    (hTable : p ∈ orientedSmallRankThreeTable)
    (hProfile : p.constituentProfile side ∈ smallConstituentProfiles) :
    (p, side) ∈ smallConstituentHits := by
  rw [← calculatedSmallConstituentHits_eq]
  apply List.mem_eraseDups.mpr
  apply List.mem_filter.mpr
  refine ⟨List.mem_flatMap.mpr ⟨p, hTable, ?_⟩, decide_eq_true hProfile⟩
  cases side <;> simp

/-- A first-constituent equation bounds the host directly. For a second
constituent, the same bound applies to the complemented orientation
whenever its parameters satisfy the equation and have positive μ. -/
theorem smallConstituentHost_order_le_460 {p : SRGParameters} {side : Bool}
    (hProfile : p.constituentProfile side ∈ smallConstituentProfiles)
    (hEquation : p.ParameterEquation) (hMu : 0 < p.nonadjacentCommon)
    (hComplEquation : p.compl.ParameterEquation) (hComplMu : 0 < p.compl.nonadjacentCommon)
    (hMuLe : p.nonadjacentCommon ≤ p.degree)
    (hN : 2 * p.degree ≤ p.order + p.nonadjacentCommon) :
    p.order ≤ 460 := by
  cases side with
  | false =>
    apply smallConstituent_host_order_le_460 (k := p.degree) (l := p.adjacentCommon)
      (m := p.nonadjacentCommon) _ hEquation hMu
    exact List.mem_append_left _ hProfile
  | true =>
    have hL : p.compl.adjacentCommon =
        (p.order - p.degree - 1) - (p.degree - p.nonadjacentCommon) - 1 := by
      unfold SRGParameters.compl
      dsimp
      omega
    have hProfileCompl :
        (p.compl.degree, p.compl.adjacentCommon) ∈ smallConstituentProfilesWithComplements := by
      apply List.mem_append_right
      have hMem : ((p.order - p.degree - 1), (p.degree - p.nonadjacentCommon)) ∈
          smallConstituentProfiles := hProfile
      exact hL ▸ List.mem_map.mpr ⟨_, hMem, rfl⟩
    exact smallConstituent_host_order_le_460 hProfileCompl hComplEquation hComplMu

end EPPAIII.Primitive
