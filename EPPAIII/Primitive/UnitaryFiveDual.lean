import EPPAIII.Primitive.PolarRankTwoArithmetic
import EPPAIII.Primitive.PolarRankTwoExclusion

/-! # Exclusion for the line graph of the rank-two Hermitian space -/

namespace EPPAIII.Primitive

/-- The dual unitary quadrangle uses (Q,t) = (q³,q²).
The SRG parameters, local cliques, and bound on the full line stabilizer
are the geometry inputs. -/
theorem unitaryFive_dual_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ a : Equiv.Perm W, IsGraphAutomorphism H a ∧ a x = y)
    (root : V) {q f : ℕ} (hq : 2 ≤ q) (hf : f ≤ q)
    (hSRG : H.IsSRGWith ((q ^ 3 + 1) * (q ^ 5 + 1)) (q ^ 3 * (q ^ 2 + 1))
      (q ^ 3 - 1) (q ^ 2 + 1))
    (hLocal : localGraph H (e root) ≃g cliqueUnion (q ^ 2 + 1) (q ^ 3))
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) ≤
      2 * f * q ^ 10 * (q ^ 2 - 1) * (q ^ 4 - 1)) : False := by
  have hRange : RankTwoPolarRange (q ^ 3) (q ^ 2) := by
    have hCube : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq _
    have hSquare : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq _
    exact Or.inl ⟨by omega, hSquare⟩
  apply polar_rankTwo_not_eppa_of_small_stabilizer G H e heppa hHalf hTrans root hRange
    _ hLocal hShape (hStabilizer.trans_lt (unitaryFive_dual_stabilizer_bound q f hq hf))
  simpa only [← pow_add, show (3 + 2 : Nat) = 5 from rfl] using hSRG

end EPPAIII.Primitive
