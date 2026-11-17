import EPPAIII.Primitive.EvenLocalRankThree
import EPPAIII.Primitive.StronglyRegularCovers

/-! # Exact-half bounds for actual selections in nonhomogeneous covers -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover

/-- A transitive nonhomogeneous cover, in either orientation, cannot
witness EPPA for a strict majority. This concerns the actual selection. -/
theorem nonhomogeneous_cover_selected_at_most_half
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hEppa : IsEPPAEmbedding G H e)
    (hTrans : HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ IsHomogeneousGraph H)
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (hCover : Nonempty (H ≃g coverGraph s t X Y) ∨
      Nonempty (H ≃g (coverGraph s t X Y)ᶜ)) :
    2 * Nat.card V ≤ Nat.card W := by
  classical
  by_contra! hStrict
  letI := Fintype.ofFinite V
  letI := Fintype.ofFinite W
  have hSize : Fintype.card W < 2 * Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card] using hStrict
  rcases transitive_eppa_at_most_double_clique_empty_or_rank_three
      G H e hEppa hTrans hSize.le (fun h => (hSize.ne h).elim) with hTop | hBot | hRank
  · exact hNonhomogeneous (homogeneous_of_complete H
      (by rw [hTop]; exact fun _ _ hne => hne))
  · exact hNonhomogeneous (homogeneous_of_edgeless H
      (by rw [hBot]; exact fun _ _ hAdj => hAdj))
  · obtain ⟨_, _, _, hSRG⟩ := rankThree_isSRG H hRank
    exact hNonhomogeneous (srg_iso_cover_homogeneous H hSRG X Y hCover)

/-- The local variant of the even-order observation in Section 8.
If the local host is a nonhomogeneous cover and the nonlocal host
has even order, the nonlocal selection has at least half its host.
If the local selection also meets half, it has exactly half. -/
theorem other_selection_meets_half_of_local_cover
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hEppa : IsEPPAEmbedding G H e)
    (hRank : HasRankThreeAutAction H)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (root : V)
    (hNonhomogeneous : ¬ IsHomogeneousGraph (localGraph H (e root)))
    {s t : ℕ} (X : CrossType) (Y : Bool)
    (hCover : Nonempty (localGraph H (e root) ≃g coverGraph s t X Y) ∨
      Nonempty (localGraph H (e root) ≃g (coverGraph s t X Y)ᶜ))
    (hEven : Even (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x})) :
    (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x}) ∧
    (Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      2 * Nat.card (G.neighborSet root) = Nat.card (H.neighborSet (e root))) := by
  have hLocal := nonhomogeneous_cover_selected_at_most_half
    (localGraph G root) (localGraph H (e root)) _ (local_eppa G H e hEppa root)
    (localGraph_transitive H hRank (e root)) hNonhomogeneous X Y hCover
  have hH := order_eq_one_add_subconstituent_orders H (e root)
  have hG := order_eq_one_add_subconstituent_orders G root
  obtain ⟨n, hn⟩ := hEven
  exact ⟨by omega, fun h => le_antisymm hLocal h⟩

end EPPAIII.Primitive
