import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.OrthogonalEightConstituents
import EPPAIII.Primitive.PolarRankTwoConstituent
import EPPAIII.Primitive.PolarRankTwoStabilizer

/-! # Rank-two polar exclusion at the actual selected root -/

namespace EPPAIII.Primitive

/-- In the rank-two geometry, the nonlocal host graph fails the induction
shape test, so the selected local neighbourhood reaches half order. -/
private theorem selected_local_at_least_half_of_rankTwoPolar
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) {Q t : ℕ} (hRange : RankTwoPolarRange Q t)
    (hSRG : H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1))
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root))) :
    Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) := by
  rcases selected_subconstituent_at_least_half G H e root hTrans hHalf with hL | hR
  · exact hL
  exfalso
  obtain ⟨hClique, hCoClique, hCover, hCoCover⟩ :=
    polar_rankTwo_actual_second_constituent_excludes_forms H hRange hSRG (e root)
  rcases hShape hR with ⟨s, b, ⟨φ⟩ | ⟨φ⟩⟩ | ⟨s, b, X, Y, ⟨φ⟩ | ⟨φ⟩⟩
  · obtain ⟨φ⟩ := φ
    exact (hClique s b).false φ
  · obtain ⟨φ⟩ := φ
    exact (hCoClique s b).false φ
  · obtain ⟨φ⟩ := φ
    exact (hCover s b X Y).false φ
  · obtain ⟨φ⟩ := φ
    exact (hCoCover s b X Y).false φ

/-- A rank-two polar root is excluded if its stabilizer is too small for
the selected local clique profile. The graph-only inputs give the local
clique union and the nonlocal SRG profile. Section 8 supplies the shape
condition only if the selected nonlocal constituent reaches half-order. -/
theorem polar_rankTwo_not_eppa_of_small_stabilizer
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) {Q t : ℕ} (hRange : RankTwoPolarRange Q t)
    (hSRG : H.IsSRGWith ((Q + 1) * (Q * t + 1)) (Q * (t + 1)) (Q - 1) (t + 1))
    (hLocalModel : localGraph H (e root) ≃g cliqueUnion (t + 1) Q)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) <
      (Q / 2).factorial ^ (t + 1)) : False := by
  have hLocalHalf := selected_local_at_least_half_of_rankTwoPolar
    G H e hHalf hTrans root hRange hSRG hShape
  have hSize : Nat.card (H.neighborSet (e root)) = (t + 1) * Q := by
    change Nat.card ↥(H.neighborSet (e root)) = _
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr hLocalModel.toEquiv
  have hTwice : 2 * ((t + 1) * (Q / 2)) ≤ (t + 1) * Q := by
    have h := Nat.mul_le_mul_left (t + 1) (show 2 * (Q / 2) ≤ Q by omega)
    rwa [← Nat.mul_assoc, Nat.mul_comm (t + 1) 2, Nat.mul_assoc] at h
  have hPos : 0 < Q / 2 := by
    rcases hRange with ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨hQ, _⟩ | ⟨hQ, _⟩ <;> omega
  have hBound := factorial_pow_le_root_stabilizer_of_local_clique_union
    G H e heppa root hLocalModel hPos (by omega)
  exact (not_lt_of_ge hBound) hStabilizer

/-- The elliptic point graph over 𝔽₅ needs the full (Q,t) local profile
instead of the rounded factorial bound at average size two. -/
theorem ellipticSixFive_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = y)
    (root : V) (hSRG : H.IsSRGWith 756 130 4 26)
    (φ : localGraph H (e root) ≃g cliqueUnion 26 5)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root)))
    (hStabilizer : Nat.card (pointwiseGraphStabilizer H {e root}) ≤ 78000000) : False := by
  have hRange : RankTwoPolarRange 5 25 := Or.inl ⟨by decide, by decide⟩
  have hLocalHalf := selected_local_at_least_half_of_rankTwoPolar G H e hHalf hTrans root
    hRange hSRG hShape
  have hOrder : Nat.card (H.neighborSet (e root)) = 130 := by
    simpa only [Nat.card_prod, Nat.card_fin] using Nat.card_congr φ.toEquiv
  have hBound := two_pow_le_root_stabilizer_of_local_clique_union
    G H e heppa root (m := 39) φ (by omega)
  exact (by decide : ¬ 2 ^ 39 ≤ 78000000) (hBound.trans hStabilizer)

end EPPAIII.Primitive
