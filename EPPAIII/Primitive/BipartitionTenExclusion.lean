import EPPAIII.Primitive.BipartitionTenConstituents
import EPPAIII.Primitive.RankThree
import EPPAIII.Primitive.RookBounds

/-! # Excluding the order-126 rank-three bipartition host -/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

private theorem bipartitionTenNonlocal_transitive
    (hRank : HasRankThreeAutAction (equalBipartitionGraph 4)) :
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (nonlocalGraph (equalBipartitionGraph 4) bipartitionTenRoot) := by
  let H := equalBipartitionGraph 4
  let r := bipartitionTenRoot
  intro u v
  obtain ⟨q, hq, hRoot, huv⟩ := rankThree_point_stabilizer H hRank r u v
    u.property.1 v.property.1 (iff_of_false u.property.2 v.property.2)
  have hPreserves (x : EqualBipartitionVertex 4) :
      (r ≠ x ∧ ¬ H.Adj r x) ↔ (r ≠ q x ∧ ¬ H.Adj r (q x)) := by
    have hNe : r ≠ x ↔ q r ≠ q x :=
      ⟨fun h heq => h (q.injective heq), fun h heq => h (congrArg q heq)⟩
    have hAdj := hq r x
    rw [hRoot] at hNe hAdj
    exact and_congr hNe hAdj.not
  exact ⟨q.subtypeEquiv hPreserves, fun x y => hq x y, Subtype.ext huv⟩

/-- A selected vertex has at most 11 selected neighbours. Hence the
100-vertex nonlocal graph would witness EPPA for a base of order at least 51.
Its unequal adjacent codegrees rule out the rank-three conclusion. -/
theorem bipartitionTen_noHalfOrderEPPA
    (hRank : HasRankThreeAutAction (equalBipartitionGraph 4)) :
    NoHalfOrderEPPA (equalBipartitionGraph 4) := by
  let H := equalBipartitionGraph 4
  let r := bipartitionTenRoot
  apply (noHalfOrderEPPA_iff H).mpr
  intro S hHalf hEPPA
  let G := H.induce S
  have hHostCard : Nat.card (EqualBipartitionVertex 4) = 126 := by
    rw [Nat.card_eq_fintype_card, bipartitionTen_order]
  have hS : 63 ≤ Nat.card S := by omega
  obtain ⟨v⟩ : Nonempty S := (Nat.card_pos_iff.mp (by omega)).1
  obtain ⟨q, hq, hqv⟩ := hRank.2.2.1 v.val r
  let φ : H ≃g H := ⟨q, fun {a b} => (hq a b).symm⟩
  let e := (Function.Embedding.subtype S).trans φ.toEquiv.toEmbedding
  have hMoved : IsEPPAEmbedding G H e := eppa_relabel_host G _ hEPPA φ
  have hRoot : e v = r := hqv
  have hLocal := order_le_maxEppaOrder _ _ _ (local_eppa G H e hMoved v)
  rw [hRoot] at hLocal
  have hRook := (maxEppaOrder_le_of_iso bipartitionTenRookIso.symm).trans
    maxEppaOrder_rookFive_le_eleven
  have hDegree : Nat.card (G.neighborSet v) ≤ 11 := hLocal.trans hRook
  let U := {x : S // v ≠ x ∧ ¬ G.Adj v x}
  have hSplit := order_eq_one_add_subconstituent_orders G v
  change Nat.card S = 1 + Nat.card (G.neighborSet v) + Nat.card U at hSplit
  have hLarge : 100 < 2 * Nat.card U := by omega
  have hNonlocal : ∃ f : U ↪ {x : EqualBipartitionVertex 4 // e v ≠ x ∧ ¬ H.Adj (e v) x},
      IsEPPAEmbedding (nonlocalGraph G v) (nonlocalGraph H (e v)) f :=
    ⟨_, nonlocal_eppa G H e hMoved v⟩
  rw [hRoot] at hNonlocal
  obtain ⟨f, hf⟩ := hNonlocal
  letI : Fintype U := Fintype.ofFinite U
  letI : DecidableEq U := Classical.decEq U
  have hStrict : Fintype.card {x : EqualBipartitionVertex 4 // r ≠ x ∧ ¬ H.Adj r x} <
      2 * Fintype.card U := by
    rw [bipartitionTenNonlocal_order, ← Nat.card_eq_fintype_card]
    exact hLarge
  rcases transitive_eppa_at_most_double_clique_empty_or_rank_three (V := U)
      (nonlocalGraph G v) (nonlocalGraph H r) f hf
      (bipartitionTenNonlocal_transitive hRank) (Nat.le_of_lt hStrict)
      (fun hEq => (hStrict.ne hEq).elim) with hTop | hBot | hRank'
  · exact bipartitionTenNonlocal_not_degenerate.1 hTop
  · exact bipartitionTenNonlocal_not_degenerate.2 hBot
  · obtain ⟨_, _, _, hSRG⟩ := rankThree_isSRG (nonlocalGraph H r) hRank'
    exact bipartitionTenNonlocal_not_srg hSRG

/-- Relabel the rank-three action and its two ordered-pair orbits. -/
private theorem bipartition_rankThree_of_iso {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ≃g H) (hRank : HasRankThreeAutAction G) :
    HasRankThreeAutAction H := by
  let f := φ.toEquiv
  have hMap (a b : V) : G.Adj a b ↔ H.Adj (f a) (f b) := φ.map_rel_iff.symm
  have hInv (a b : W) : H.Adj a b ↔ G.Adj (f.symm a) (f.symm b) := by
    simpa only [Equiv.apply_symm_apply] using (hMap (f.symm a) (f.symm b)).symm
  let transport (q : Equiv.Perm V) : Equiv.Perm W := (f.symm.trans q).trans f
  have hTransport (q : Equiv.Perm V) (hq : IsGraphAutomorphism G q) :
      IsGraphAutomorphism H (transport q) := by
    intro a b
    exact (hInv a b).trans ((hq _ _).trans (hMap _ _))
  have hSend (q : Equiv.Perm V) (a b : W) (h : q (f.symm a) = f.symm b) :
      transport q a = b := by
    change f (q (f.symm a)) = b
    rw [h, f.apply_symm_apply]
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hncd⟩, hTrans, hPairs⟩ := hRank
  refine ⟨⟨f a, f b, (hMap _ _).mp hab⟩,
    ⟨f c, f d, f.injective.ne hcd, (hMap _ _).not.mp hncd⟩, ?_, ?_⟩
  · intro u v
    obtain ⟨q, hq, h⟩ := hTrans (f.symm u) (f.symm v)
    exact ⟨transport q, hTransport q hq, hSend q u v h⟩
  · intro u v x y huv hxy hAdj
    obtain ⟨q, hq, hu, hv⟩ := hPairs (f.symm u) (f.symm v) (f.symm x) (f.symm y)
      (f.symm.injective.ne huv) (f.symm.injective.ne hxy)
      ((hInv u v).symm.trans (hAdj.trans (hInv x y)))
    exact ⟨transport q, hTransport q hq, hSend q u x hu, hSend q v y hv⟩

private theorem bipartition_rankThree_compl {W : Type*} {H : SimpleGraph W}
    (hRank : HasRankThreeAutAction H) : HasRankThreeAutAction Hᶜ := by
  classical
  obtain ⟨⟨a, b, hab⟩, ⟨c, d, hcd, hncd⟩, hTrans, hPairs⟩ := hRank
  refine ⟨⟨c, d, hcd, hncd⟩, ⟨a, b, H.ne_of_adj hab, fun h => h.2 hab⟩,
    transitive_complement H hTrans, ?_⟩
  intro u v x y huv hxy hAdj
  have hSame : (¬ H.Adj u v) ↔ ¬ H.Adj x y :=
    ⟨fun h => (hAdj.mp ⟨huv, h⟩).2, fun h => (hAdj.mpr ⟨hxy, h⟩).2⟩
  obtain ⟨q, hq, hu, hv⟩ := hPairs u v x y huv hxy (not_iff_not.mp hSame)
  exact ⟨q, graphAutomorphism_complement H q hq, hu, hv⟩

/-- Exclude a classified rank-three host in either bipartition orientation. -/
theorem noHalfOrderEPPA_of_bipartitionTen_model {W : Type*} [Finite W]
    (H : SimpleGraph W) (hRank : HasRankThreeAutAction H)
    (hModel : IsModelUpToComplement H (equalBipartitionGraph 4)) : NoHalfOrderEPPA H := by
  rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (bipartitionTen_noHalfOrderEPPA (bipartition_rankThree_of_iso φ hRank)).of_iso φ
  · have hModelRank := bipartition_rankThree_compl (bipartition_rankThree_of_iso φ hRank)
    rw [compl_compl] at hModelRank
    exact (bipartitionTen_noHalfOrderEPPA hModelRank).compl.of_iso φ

end EPPAIII.Primitive
