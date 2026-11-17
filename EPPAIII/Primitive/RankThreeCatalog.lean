import EPPAIII.Primitive.RankThree
import EPPAIII.Primitive.EqualBipartitionModels
import EPPAIII.Primitive.Triangular

/-!
# Explicit boundary for the external rank-three classification

This interface projects the Brouwer–Van Maldeghem Chapter 11 results
from permutation-group representations to graph isomorphism types.
The classification hypothesis has no EPPA, selected subgraph, or
local-graph hypotheses. Until all entries of the external model
catalogue are specified, this is an integration interface and not a
complete Lean transcription of that chapter.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open scoped BigOperators

universe u

/-- The rook graph on an n-by-n lattice. -/
def rookGraph (n : ℕ) : SimpleGraph (Fin n × Fin n) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, h.2.elim (fun h => .inl h.symm) (fun h => .inr h.symm)⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- The vertices of T(n) are precisely the two-element subsets of [n]. -/
abbrev TriangularVertex (n : ℕ) := TwoSet (Fin n)

/-- Use the same triangular graph as the EPPA witness theorem. -/
abbrev triangularModel (n : ℕ) : SimpleGraph (TriangularVertex n) :=
  triangularGraph (Fin n)

/-- The nonsingular vectors for the plus-type quadratic form
Q(x,y)=x·y on F₂⁴ × F₂⁴. Over F₂ vectors represent projective
points without an additional scalar quotient. -/
abbrev NonsingularOrthogonalEightVertex :=
  {p : (Fin 4 → ZMod 2) × (Fin 4 → ZMod 2) //
    (∑ i, p.1 i * p.2 i) = 1}

/-- The degree-56 orientation of NO⁺₈(2), in which the polar form is
nonzero. Its complementary degree is 63. -/
def nonsingularOrthogonalEightGraph :
    SimpleGraph NonsingularOrthogonalEightVertex where
  Adj x y := x ≠ y ∧ (∑ i, (x.val.1 i * y.val.2 i + y.val.1 i * x.val.2 i)) = 1
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm, by simpa only [add_comm] using h.2⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

/-- Graph isomorphism, allowing either orientation of the model.
The disjunction keeps track of which orientation is returned. -/
def IsModelUpToComplement {V W : Type*} (H : SimpleGraph V) (K : SimpleGraph W) :
    Prop :=
  Nonempty (H ≃g K) ∨ Nonempty (H ≃g Kᶜ)

/-- The parts of the external catalogue whose graph constructions
remain separate model data. The index in affineA3To11 i denotes case A(i+3). -/
inductive RankThreeExternalCase
  | classicalSingularPoints
  | classicalMaximalSingularSubspaces
  | classicalNonsingularPoints
  | classicalNonsingularHyperplanes
  | classicalIndividualModels
  | grassmann
  | exceptionalE6
  | exceptionalTable
  | sporadicTable
  | affineSemilinearOne
  | affineA3To11 (i : Fin 9)
  | affineExtraspecial
  | affineExceptional
  deriving DecidableEq

/-- A model represented on Fin of its order. This representation allows
multiple distinct models of equal order or equal SRG parameters. -/
abbrev FiniteGraphModel := Σ n : ℕ, SimpleGraph (Fin n)

/-- The residual catalogue data. Each set is to be populated from the
corresponding graph constructions, without filtering by EPPA. -/
abbrev RankThreeCatalog := RankThreeExternalCase → Set FiniteGraphModel

/-- The graph-only output of the published primitive rank-three
classification. Lattice graphs (including affine A2), triangular
graphs (including repeated socle cases), and the three individual
alternating-socle models are fixed constructions. -/
def InRankThreeCatalog {W : Type*} (catalog : RankThreeCatalog)
    (H : SimpleGraph W) : Prop :=
  (∃ n ≥ 3, IsModelUpToComplement H (rookGraph n)) ∨
  (∃ n ≥ 5, IsModelUpToComplement H (triangularModel n)) ∨
  IsModelUpToComplement H (equalBipartitionGraph 3) ∨
  IsModelUpToComplement H (equalBipartitionGraph 4) ∨
  IsModelUpToComplement H nonsingularOrthogonalEightGraph ∨
  (∃ c : RankThreeExternalCase, ∃ model ∈ catalog c,
    IsModelUpToComplement H model.2)

/-- The sole classification hypothesis of this interface. The full
automorphism action is primitive and has rank three; the mathematical
conclusion is membership in the graph catalogue up to complementation. -/
def RankThreeClassification (catalog : RankThreeCatalog) : Prop :=
  ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
    IsPrimitiveAutAction H → HasRankThreeAutAction H → InRankThreeCatalog catalog H

/-- Apply the external catalogue only after the Lean proof of the
small-host rank-three reduction. The two degenerate host cases are
kept exactly as in the manuscript's prop:rank3. -/
theorem small_primitive_eppa_in_rankThreeCatalog
    {V : Type*} {W : Type u} [Fintype V] [DecidableEq V] [Fintype W]
    (catalog : RankThreeCatalog) (hClassification : RankThreeClassification.{u} catalog)
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hBound : Fintype.card W ≤ 2 * Fintype.card V)
    (hPrimitive : IsPrimitiveAutAction H) :
    H = ⊤ ∨ H = ⊥ ∨ InRankThreeCatalog catalog H := by
  rcases transitive_eppa_at_most_double_clique_empty_or_rank_three
      G H e heppa hTrans hBound (fun _ => hPrimitive) with hTop | hBot | hRank
  · exact .inl hTop
  · exact .inr (.inl hBot)
  · exact .inr (.inr (hClassification H hPrimitive hRank))

end EPPAIII.Primitive
