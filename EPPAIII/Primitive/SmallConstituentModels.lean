import EPPAIII.Primitive.BinaryOrthogonalModels
import EPPAIII.Primitive.RankThreeCatalog
import EPPAIII.Primitive.SmallConstituentGraphScreen
import EPPAIII.Primitive.SmallRankThreeParameterRecognition

/-!
# Graph models of the screened Table 11.8 rows

The 21 oriented host tuples compatible with a small constituent each
have a specific representative from Table 11.8. Graph identification
is requested as an explicit external classification input, separate
from the certified numerical screen.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

universe u

private def symmetricDifferenceGraph {W : Type*} [Sub W] (S : Set W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ (x - y ∈ S ∨ y - x ∈ S)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The Paley graph of prime order q ≡ 1 mod 4, using squares modulo q.
Only q = 17, 37, or 41 is used by the lookup below. At these orders
the square set is invariant under negation. -/
def paleyPrimeModel (q : Nat) : SimpleGraph (ZMod q) :=
  symmetricDifferenceGraph {x | ∃ y : ZMod q, y * y = x}

/-- Paley(25) over the quadratic extension with basis (1,t), t²=2.
The polynomial is irreducible over F₅ as 2 is not a square. -/
def paleyTwentyFiveModel : SimpleGraph (ZMod 5 × ZMod 5) :=
  symmetricDifferenceGraph {x | ∃ a b : ZMod 5,
    (a * a + 2 * b * b, 2 * a * b) = x}

/-- The folded 5-cube, with five nonzero generators on F₂⁴.
This is the degree-5 Clebsch orientation used in R17. -/
def foldedFiveCubeModel : SimpleGraph (Fin 16) where
  Adj x y := x ≠ y ∧ (x.val ^^^ y.val) ∈ [1, 2, 4, 8, 15]
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Nat.xor_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The 15 pairs and two sixes in the Schläfli graph construction. -/
abbrev SchlaefliVertex := (Bool × Fin 6) ⊕ TwoSet (Fin 6)

private def schlaefliRelated : SchlaefliVertex → SchlaefliVertex → Prop
  | .inl (b, i), .inl (c, j) => (b = c ∧ i ≠ j) ∨ (b ≠ c ∧ i = j)
  | .inl (_, i), .inr p => i ∉ p.val
  | .inr p, .inl (_, i) => i ∉ p.val
  | .inr p, .inr q => (p.val ∩ q.val).card = 1

/-- The degree-16 Schläfli graph from the double-six construction in
Brouwer–Van Maldeghem §10.10. Its complement appears in the screen. -/
def schlaefliModel : SimpleGraph SchlaefliVertex where
  Adj x y := x ≠ y ∧ schlaefliRelated x y
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rcases x with ⟨b, i⟩ | p <;> rcases y with ⟨c, j⟩ | q
    · simpa [schlaefliRelated, eq_comm] using h.2
    · exact h.2
    · exact h.2
    · simpa [schlaefliRelated, Finset.inter_comm] using h.2
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel schlaefliModel.Adj := fun a b => by
  change Decidable (a ≠ b ∧ schlaefliRelated a b)
  rcases a with ⟨r, i⟩ | p <;> rcases b with ⟨s, j⟩ | q <;>
    unfold schlaefliRelated <;> infer_instance

/-- Table labels for the screened, oriented host models. -/
inductive SmallConstituentHostModel
  | rook (n : Nat) (complemented : Bool)
  | triangularComplement (n : Nat)
  | paleyPrime (q : Nat)
  | paleyTwentyFive
  | foldedFiveCube
  | schlaefliComplement
  | equalBipartitionEight
  | orthogonalSixMinus
  | affineOrthogonalSixMinusComplement
  deriving DecidableEq

namespace SmallConstituentHostModel

def Vertex : SmallConstituentHostModel → Type
  | .rook n _ => Fin n × Fin n
  | .triangularComplement n => TriangularVertex n
  | .paleyPrime q => ZMod q
  | .paleyTwentyFive => ZMod 5 × ZMod 5
  | .foldedFiveCube => Fin 16
  | .schlaefliComplement => SchlaefliVertex
  | .equalBipartitionEight => EqualBipartitionVertex 3
  | .orthogonalSixMinus => OrthogonalSixVertex false false
  | .affineOrthogonalSixMinusComplement => Fin 64

def graph : (m : SmallConstituentHostModel) → SimpleGraph m.Vertex
  | .rook n false => rookGraph n
  | .rook n true => (rookGraph n)ᶜ
  | .triangularComplement n => (triangularModel n)ᶜ
  | .paleyPrime q => paleyPrimeModel q
  | .paleyTwentyFive => paleyTwentyFiveModel
  | .foldedFiveCube => foldedFiveCubeModel
  | .schlaefliComplement => schlaefliModelᶜ
  | .equalBipartitionEight => equalBipartitionGraph 3
  | .orthogonalSixMinus => orthogonalSixGraph false false
  | .affineOrthogonalSixMinusComplement => (vectorOrthogonalSixGraph false)ᶜ

end SmallConstituentHostModel

/-- The oriented graph label attached to each screened parameter tuple
by Table 11.8. Equal parameters in other rows are still admissible in
the numerical table and need no graph identity for this argument. -/
def smallConstituentHostModel : SRGParameters → Option SmallConstituentHostModel
  | ⟨15, 6, 1, 3⟩ => some (.triangularComplement 6)
  | ⟨16, 5, 0, 2⟩ => some .foldedFiveCube
  | ⟨16, 6, 2, 2⟩ => some (.rook 4 false)
  | ⟨16, 9, 4, 6⟩ => some (.rook 4 true)
  | ⟨17, 8, 3, 4⟩ => some (.paleyPrime 17)
  | ⟨21, 10, 3, 6⟩ => some (.triangularComplement 7)
  | ⟨25, 8, 3, 2⟩ => some (.rook 5 false)
  | ⟨25, 12, 5, 6⟩ => some .paleyTwentyFive
  | ⟨27, 10, 1, 5⟩ => some .schlaefliComplement
  | ⟨28, 15, 6, 10⟩ => some (.triangularComplement 8)
  | ⟨35, 16, 6, 8⟩ => some .equalBipartitionEight
  | ⟨36, 10, 4, 2⟩ => some (.rook 6 false)
  | ⟨36, 15, 6, 6⟩ => some .orthogonalSixMinus
  | ⟨37, 18, 8, 9⟩ => some (.paleyPrime 37)
  | ⟨41, 20, 9, 10⟩ => some (.paleyPrime 41)
  | ⟨49, 12, 5, 2⟩ => some (.rook 7 false)
  | ⟨55, 36, 21, 28⟩ => some (.triangularComplement 11)
  | ⟨64, 36, 20, 20⟩ => some .affineOrthogonalSixMinusComplement
  | ⟨66, 45, 28, 36⟩ => some (.triangularComplement 12)
  | ⟨100, 18, 8, 2⟩ => some (.rook 10 false)
  | ⟨121, 20, 9, 2⟩ => some (.rook 11 false)
  | _ => none

theorem smallConstituentHostModel_exists {p : SRGParameters} {side : Bool}
    (hHit : (p, side) ∈ smallConstituentHits) :
    ∃ m, smallConstituentHostModel p = some m := by
  have hAll : smallConstituentHits.all
      (fun (p, _) => (smallConstituentHostModel p).isSome) = true := by decide
  exact Option.isSome_iff_exists.mp (List.all_eq_true.mp hAll (p, side) hHit)

/-- The graph identities of the 21 screened Table 11.8 tuples.
Primitivity and graph rank three are essential to this assertion. -/
def SmallRankThreeModelIdentification : Prop :=
  ∀ {V : Type u} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (p : SRGParameters) (m : SmallConstituentHostModel),
    IsPrimitiveAutAction H → HasRankThreeAutAction H →
    H.IsSRGWith p.order p.degree p.adjacentCommon p.nonadjacentCommon →
    smallConstituentHostModel p = some m → Nonempty (H ≃g m.graph)

/-- A primitive rank-three host with a small actual constituent
belongs to the oriented, concrete part of the published catalogue.
The two external inputs concern only the host graph. -/
theorem primitiveRankThree_smallConstituent_hostModel {V : Type u} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hPrim : IsPrimitiveAutAction H) (hRank : HasRankThreeAutAction H)
    (hCoverage : SmallRankThreeParameterCoverage.{u})
    (hIdentify : SmallRankThreeModelIdentification.{u})
    (root : V) (side : Bool) (q : Nat × Nat)
    (hProfile : HasRegularProfile (constituentGraph H root side) q)
    (hSmall : q ∈ smallConstituentProfiles) :
    ∃ p m, (p, side) ∈ smallConstituentHits ∧
      smallConstituentHostModel p = some m ∧ Nonempty (H ≃g m.graph) := by
  obtain ⟨k, l, μ, hSRG⟩ := rankThree_isSRG H hRank
  let p : SRGParameters := ⟨Fintype.card V, k, l, μ⟩
  have hConnected := primitive_rankThree_connected H hPrim hRank
  have hHit := smallConstituentScreen_of_srg H p hSRG
    hConnected.1.preconnected hConnected.2.preconnected hRank.1 hRank.2.1
    (hCoverage H p hPrim hRank hSRG) root side q hProfile hSmall
  obtain ⟨m, hm⟩ := smallConstituentHostModel_exists hHit
  exact ⟨p, m, hHit, hm, hIdentify H p m hPrim hRank hSRG hm⟩

end EPPAIII.Primitive
