import EPPAIII.Primitive.BinaryOrthogonalModels
import EPPAIII.Primitive.LocalRecognitionArithmetic
import EPPAIII.Primitive.Triangular

/-!
# The two small Kneser local recognition cases

The locally Kneser catalogue disjunctions are graph-specific inputs. A rooted
isomorphism determines the host valency and its adjacent common-neighbour
count. The checked strongly regular parameter identity then removes the three
exceptional orders and preserves the remaining graph isomorphisms.
-/

namespace EPPAIII.Primitive

private instance decidableComplTriangular (m : ℕ) :
    DecidableRel (triangularGraph (Fin m))ᶜ.Adj := by
  intro a b
  change Decidable (a ≠ b ∧ ¬ (a ≠ b ∧ ∃ c : Fin m, c ∈ a.val ∧ c ∈ b.val))
  infer_instance

private theorem srg_parameters_of_rooted_local_iso {V U : Type*}
    [Fintype V] [Fintype U] (H : SimpleGraph V) [DecidableRel H.Adj]
    (K : SimpleGraph U) [DecidableRel K.Adj] {n k l μ : ℕ}
    (h : H.IsSRGWith n k l μ) (root : V)
    (iso : K ≃g H.induce (H.neighborSet root)) (u : U) :
    k = Fintype.card U ∧ l = K.degree u := by
  let a := iso u
  let common : (H.induce (H.neighborSet root)).neighborSet a ≃ H.commonNeighbors root a :=
    { toFun y := ⟨y.val.val, y.val.property, y.property⟩
      invFun y := ⟨⟨y.val, y.property.1⟩, y.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  constructor
  · rw [← h.regular root, ← H.card_neighborSet_eq_degree]
    exact iso.card_eq.symm
  · rw [← h.of_adj root a a.property, ← Fintype.card_congr common,
      ← Fintype.card_congr (iso.mapNeighborSet u), ← K.card_neighborSet_eq_degree]

/-- For a strongly regular graph locally `KG(5,2)`, only the `KG(7,2)`
branch survives the published locally Petersen candidate list. -/
theorem locallyComplementTriangular_five_recognition
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {n k l μ : ℕ} (h : H.IsSRGWith n k l μ) (root : V)
    (iso : (triangularGraph (Fin 5))ᶜ ≃g H.induce (H.neighborSet root))
    (hCandidates : Nonempty (H ≃g (triangularGraph (Fin 7))ᶜ) ∨ n = 63 ∨ n = 65) :
    Nonempty (H ≃g (triangularGraph (Fin 7))ᶜ) := by
  let u : TwoSet (Fin 5) := ⟨{0, 1}, by decide⟩
  obtain ⟨hk, hl⟩ := srg_parameters_of_rooted_local_iso H _ h root iso u
  change k = 10 at hk
  change l = 3 at hl
  subst k
  subst l
  rcases hCandidates with hK | hWrong
  · exact hK
  · have hn := locallyComplementTriangular_five_srg_order H h (Or.inr hWrong)
    omega

/-- For a strongly regular graph locally `KG(6,2)`, the published candidate
of order 32 is impossible. The two remaining graph models are preserved. -/
theorem locallyComplementTriangular_six_recognition
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {n k l μ : ℕ} (h : H.IsSRGWith n k l μ) (root : V)
    (iso : (triangularGraph (Fin 6))ᶜ ≃g H.induce (H.neighborSet root))
    (hCandidates : Nonempty (H ≃g (triangularGraph (Fin 8))ᶜ) ∨ n = 32 ∨
      Nonempty (H ≃g orthogonalSixGraph false false)) :
    Nonempty (H ≃g (triangularGraph (Fin 8))ᶜ) ∨
      Nonempty (H ≃g orthogonalSixGraph false false) := by
  let u : TwoSet (Fin 6) := ⟨{0, 1}, by decide⟩
  obtain ⟨hk, hl⟩ := srg_parameters_of_rooted_local_iso H _ h root iso u
  change k = 15 at hk
  change l = 6 at hl
  subst k
  subst l
  rcases hCandidates with hK | hWrong | hOrth
  · exact Or.inl hK
  · have hn := locallyComplementTriangular_six_srg_order H h (Or.inr (Or.inl hWrong))
    omega
  · exact Or.inr hOrth

end EPPAIII.Primitive
