import EPPAIII.Primitive.BinaryPolarCycles
import EPPAIII.Primitive.CliqueExtension
import EPPAIII.Primitive.RankThreeCases
import EPPAIII.TwoGraphs.TaylorFibresDistance

/-! # Binary polar exclusions from the rooted model identifications -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The three kinds of extended form appearing in the binary rooted
constituent descriptions. -/
inductive BinaryPolarBaseChart
  | orthogonal (plus singular : Bool) (extraPairs : ℕ)
  | affineOrthogonal (plus : Bool) (extraPairs : ℕ)
  | symplectic (extraPairs : ℕ)

def BinaryPolarBaseChart.model : BinaryPolarBaseChart → Σ V : Type, SimpleGraph V
  | .orthogonal plus singular m => ⟨_, binaryOrthogonalExtendedGraph plus singular m⟩
  | .affineOrthogonal plus m => ⟨_, binaryAffineOrthogonalExtendedGraph plus m⟩
  | .symplectic m => ⟨_, binarySymplecticExtendedGraph m⟩

private def BinaryPolarBaseChart.pentagon (base : BinaryPolarBaseChart) :
    cycleGraph 5 ↪g base.model.2 :=
  match base with
  | .orthogonal plus singular m => binaryOrthogonalExtended_fiveCycle plus singular m
  | .affineOrthogonal plus m => binaryAffineOrthogonalExtended_fiveCycle plus m
  | .symplectic m => binarySymplecticExtended_fiveCycle m

/-- A rooted binary polar model is one of the base charts, its two-clique
extension, or its Taylor extension. -/
inductive BinaryPolarConstituentChart
  | base (base : BinaryPolarBaseChart)
  | clique (base : BinaryPolarBaseChart)
  | taylor (base : BinaryPolarBaseChart)

def BinaryPolarConstituentChart.model : BinaryPolarConstituentChart → Σ V : Type, SimpleGraph V
  | .base chart => chart.model
  | .clique chart => ⟨_, cliqueExtension Bool chart.model.2⟩
  | .taylor chart => ⟨_, TwoGraphs.taylorPairGraph chart.model.2⟩

private def cliqueBottomEmbedding {V : Type*} (H : SimpleGraph V) :
    H ↪g cliqueExtension Bool H where
  toFun x := (false, x)
  inj' := fun _ _ h => congrArg Prod.snd h
  map_rel_iff' := by simp [cliqueExtension]

private def taylorBottomEmbedding {V : Type*} (H : SimpleGraph V) :
    H ↪g TwoGraphs.taylorPairGraph H where
  toFun x := (false, x)
  inj' := fun _ _ h => congrArg Prod.snd h
  map_rel_iff' := by
    intro x y
    change (x ≠ y ∧ (H.Adj x y ↔ false = false)) ↔ H.Adj x y
    simp only [iff_true]
    exact ⟨And.right, fun h => ⟨h.ne, h⟩⟩

private def BinaryPolarConstituentChart.pentagon (chart : BinaryPolarConstituentChart) :
    cycleGraph 5 ↪g chart.model.2 :=
  match chart with
  | .base base => base.pentagon
  | .clique base => (cliqueBottomEmbedding base.model.2).comp base.pentagon
  | .taylor base => (taylorBottomEmbedding base.model.2).comp base.pentagon

/-- Published binary polar constituent identities supply a chart in each
of the two actual rooted graphs. The input consists of graph isomorphisms. -/
def HasBinaryPolarConstituentCharts {V : Type*} (H : SimpleGraph V) : Prop :=
  ∀ r, (∃ K : BinaryPolarConstituentChart, Nonempty (localGraph H r ≃g K.model.2)) ∧
    (∃ K : BinaryPolarConstituentChart, Nonempty (nonlocalGraph H r ≃g K.model.2))

/-- All higher binary singular, nonsingular and affine orthogonal cases
whose constituents have the binary charts violate the shape condition. -/
theorem binaryPolar_constituents_exclude_forms {V : Type*} {H : SimpleGraph V}
    (hCharts : HasBinaryPolarConstituentCharts H) (root : V) :
    ¬ HasCliqueUnionOrCoverModel (localGraph H root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph H root) := by
  obtain ⟨⟨K, ⟨φ⟩⟩, ⟨L, ⟨ψ⟩⟩⟩ := hCharts root
  exact ⟨not_cliqueUnionOrCover_of_fiveCycle ((SimpleGraph.Iso.toEmbedding φ.symm).comp K.pentagon),
    not_cliqueUnionOrCover_of_fiveCycle ((SimpleGraph.Iso.toEmbedding ψ.symm).comp L.pentagon)⟩

end EPPAIII.Primitive
