import EPPAIII.EPPA.HostRelabel
import EPPAIII.Primitive.MathieuTwentyTwo

/-!
# The Higman–Sims exclusion

The upper bound for the second constituent forces at least eleven
selected vertices in the independent first constituent.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

/-- The constituent bound and the point stabilizer order give the
Higman–Sims exclusion for the actual selected embedding. -/
theorem higmanSims_not_eppa_embedding {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (h : H.IsSRGWith 100 22 0 6)
    (hNonlocal : ∀ r, maxEppaOrder (nonlocalGraph H r) ≤ 38)
    (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 887040)
    (e : V ↪ W) (hLarge : 50 ≤ Nat.card V) :
    ¬ IsEPPAEmbedding G H e := by
  classical
  intro heppa
  let _ : Fintype V := Fintype.ofFinite V
  have hV : 50 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hLarge
  have _ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let root : V := Classical.choice inferInstance
  let N := {x : V // root ≠ x ∧ ¬ G.Adj root x}
  have hLocalEPPA := nonlocal_eppa G H e heppa root
  have hN : Fintype.card N ≤ 38 := by
    rw [← Nat.card_eq_fintype_card]
    exact (order_le_maxEppaOrder _ _ _ hLocalEPPA).trans (hNonlocal (e root))
  have hSplit : Fintype.card V =
      1 + Fintype.card (G.neighborSet root) + Fintype.card N := by
    simpa only [Nat.card_eq_fintype_card] using order_eq_one_add_subconstituent_orders G root
  have hLocalOrder : 11 ≤ Nat.card (G.neighborSet root) := by
    rw [Nat.card_eq_fintype_card]
    omega
  have hIndependent : localGraph G root = ⊥ := by
    ext a b
    change G.Adj a.val b.val ↔ False
    constructor
    · intro hab
      have hZero := h.of_adj _ _ ((heppa.1 root a.val).mp a.property)
      have hPos : 0 < Fintype.card (H.commonNeighbors (e root) (e a.val)) :=
        Fintype.card_pos_iff.mpr ⟨⟨e b.val, H.mem_commonNeighbors.mpr
          ⟨(heppa.1 root b.val).mp b.property, (heppa.1 a.val b.val).mp hab⟩⟩⟩
      omega
    · exact False.elim
  have hDiv := factorial_dvd_rootStabilizer_card_of_homogeneous_subset
    G H e heppa root (G.neighborSet root) (G.loopless.irrefl root)
    (fun _ hx _ hy => iff_of_true hx hy) (Or.inr hIndependent) hLocalOrder
  rw [hStabilizer (e root)] at hDiv
  exact (show ¬ Nat.factorial 11 ∣ 887040 by decide) hDiv

/-- A specified isomorphism of each second constituent with the M₂₂
model supplies its EPPA bound. -/
theorem higmanSims_maxEppaOrder_le_of_m22_model {W X : Type*} [Fintype W] [Fintype X]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h : H.IsSRGWith 100 22 0 6)
    (M : SimpleGraph X) [DecidableRel M.Adj] (hM : M.IsSRGWith 77 16 0 4)
    (hMRank : HasRankThreeAutAction M)
    (hMStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer M {r}) = 11520)
    (hModel : ∀ r, Nonempty (nonlocalGraph H r ≃g M))
    (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 887040) :
    maxEppaOrder H ≤ 49 := by
  have hSecond (r : W) : maxEppaOrder (nonlocalGraph H r) ≤ 38 := by
    obtain ⟨φ⟩ := hModel r
    obtain ⟨S, hOrder, heppa⟩ := maxEppaOrder_attained (nonlocalGraph H r)
    have hTransport := eppa_relabel_host _ _ heppa φ
    have hBound := order_le_maxEppaOrder _ _ _ hTransport
    rw [hOrder] at hBound
    exact hBound.trans (mathieuTwentyTwo_maxEppaOrder_le M hM hMRank hMStabilizer)
  obtain ⟨S, hOrder, heppa⟩ := maxEppaOrder_attained H
  by_contra! hLarge
  exact higmanSims_not_eppa_embedding (H.induce S) H h hSecond hStabilizer
    (Function.Embedding.subtype S) (by omega) heppa

end EPPAIII.Primitive
