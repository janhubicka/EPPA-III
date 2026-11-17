import EPPAIII.Primitive.ConstituentShapeReduction
import EPPAIII.Primitive.CoverHalfReduction
import EPPAIII.BlockSystems.TransitiveClusterHomogeneity

/-!
# The exact-half and mixed-parity alternatives in Section 8

If neither rooted constituent is homogeneous, any one whose actual
selected copy has at least half the vertices is a cover in some
orientation, and its selected copy has exactly half the vertices.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover

private theorem cluster_of_cliqueUnion_iso {W : Type*} {H : SimpleGraph W} {s t : ℕ}
    (φ : H ≃g cliqueUnion s t) : IsClusterGraph H := by
  intro a b c hab hbc hac
  have hAB : (cliqueUnion s t).Adj (φ a) (φ b) := φ.map_adj_iff.mpr hab
  have hBC : (cliqueUnion s t).Adj (φ b) (φ c) := φ.map_adj_iff.mpr hbc
  have hIndex := hAB.1.trans hBC.1
  apply φ.map_adj_iff.mp
  refine ⟨hIndex, fun h => ?_⟩
  exact hac (φ.injective (Prod.ext hIndex h))

private theorem nonhomogeneous_form_is_cover {W : Type*} [Fintype W]
    {H : SimpleGraph W} (hTrans : HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph H)
    (hShape : HasCliqueUnionOrCoverModel H) :
    ∃ s t X Y, IsModelUpToComplement H (coverGraph s t X Y) := by
  rcases hShape with ⟨s, t, hModel⟩ | hCover
  · rcases hModel with hModel | hModel
    · obtain ⟨φ⟩ := hModel
      exact (hNonhomogeneous
        (vertex_transitive_cluster_isHomogeneous H hTrans (cluster_of_cliqueUnion_iso φ))).elim
    · obtain ⟨φ⟩ := hModel
      have ψ : Hᶜ ≃g cliqueUnion s t := by
        simpa only [compl_compl] using complHostIso φ
      exact (hNonhomogeneous ((homogeneous_complement_iff H).mpr
        (vertex_transitive_cluster_isHomogeneous Hᶜ (transitive_complement H hTrans)
          (cluster_of_cliqueUnion_iso ψ)))).elim
  · exact hCover

private theorem nonhomogeneous_form_exact_half {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (hEPPA : IsEPPAEmbedding G H e) (hTrans : HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph H)
    (hShape : HasCliqueUnionOrCoverModel H) (hHalf : Nat.card W ≤ 2 * Nat.card V) :
    (∃ s t X Y, IsModelUpToComplement H (coverGraph s t X Y)) ∧
      2 * Nat.card V = Nat.card W := by
  let := Fintype.ofFinite W
  obtain ⟨s, t, X, Y, h⟩ := nonhomogeneous_form_is_cover hTrans hNonhomogeneous hShape
  exact ⟨⟨s, t, X, Y, h⟩,
    le_antisymm (nonhomogeneous_cover_selected_at_most_half
      G H e hEPPA hTrans hNonhomogeneous X Y h) hHalf⟩

/-- Complete parity alternative for two nonhomogeneous subconstituents.
Each implication on the shapes is required only for an actual selected
copy meeting its half-order bound, as supplied by smaller-pair minimality. -/
theorem nonhomogeneous_constituents_exactHalves_or_mixedParity
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (hPair : SmallEPPAPair G H e) (hRank : HasRankThreeAutAction H) (root : V)
    (hNonhomogeneous₁ : ¬ IsHomogeneousGraph (localGraph H (e root)))
    (hNonhomogeneous₂ : ¬ IsHomogeneousGraph (nonlocalGraph H (e root)))
    (hShape₁ : Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      HasCliqueUnionOrCoverModel (localGraph H (e root)))
    (hShape₂ : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      HasCliqueUnionOrCoverModel (nonlocalGraph H (e root))) :
    let n₁ := Nat.card (H.neighborSet (e root))
    let n₂ := Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x}
    let m₁ := Nat.card (G.neighborSet root)
    let m₂ := Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x}
    ((∃ s t X Y, IsModelUpToComplement (localGraph H (e root)) (coverGraph s t X Y)) ∧
      (∃ s t X Y, IsModelUpToComplement (nonlocalGraph H (e root)) (coverGraph s t X Y)) ∧
      2 * m₁ = n₁ ∧ 2 * m₂ = n₂) ∨
    (2 * m₁ = n₁ ∧ n₂ % 2 = 1) ∨
    (n₁ % 2 = 1 ∧ 2 * m₂ = n₂) := by
  dsimp only
  have hLocal (hHalf : Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root)) :=
    nonhomogeneous_form_exact_half (local_eppa G H e hPair.eppa root)
      (localGraph_transitive H hRank (e root)) hNonhomogeneous₁ (hShape₁ hHalf) hHalf
  have hOther (hHalf : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x}) :=
    nonhomogeneous_form_exact_half (nonlocal_eppa G H e hPair.eppa root)
      (nonlocalGraph_transitive H hRank (e root)) hNonhomogeneous₂ (hShape₂ hHalf) hHalf
  have hSizeH := order_eq_one_add_subconstituent_orders H (e root)
  have hSizeG := order_eq_one_add_subconstituent_orders G root
  have hTotal := hPair.halfOrder
  rw [hSizeH, hSizeG] at hTotal
  have hSome := selected_subconstituent_at_least_half G H e root hPair.transitive hPair.halfOrder
  rcases subconstituent_exactHalves_or_mixedParity hTotal hSome
    (fun h => (hLocal h).2) (fun h => (hOther h).2) with ⟨hL, hN⟩ | hMixed
  · exact Or.inl ⟨(hLocal hL.ge).1, (hOther hN.ge).1, hL, hN⟩
  · exact Or.inr hMixed

end EPPAIII.Primitive
