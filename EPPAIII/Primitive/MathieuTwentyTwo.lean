import EPPAIII.Primitive.EvenLocalRankThree
import EPPAIII.Primitive.FactorialStabilizer
import EPPAIII.Primitive.SmallConstituentGraphScreen
import Mathlib.Data.Fintype.EquivFin

/-!
# The M₂₂ exclusion

The nonlocal constituent has order 60 and degree 12 and is triangle-free.
These parameters are incompatible with a rank-three action on it. At
least eight selected vertices then occur in the independent first
constituent, giving a factorial obstruction in the point stabilizer.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems

private theorem triangleFree_of_srg {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {n d m : ℕ}
    (h : H.IsSRGWith n d 0 m) {a b c : W} (hab : H.Adj a b) (hac : H.Adj a c) :
    ¬ H.Adj b c := by
  intro hbc
  have hZero := h.of_adj a b hab
  have hPos : 0 < Fintype.card (H.commonNeighbors a b) :=
    Fintype.card_pos_iff.mpr ⟨⟨c, H.mem_commonNeighbors.mpr ⟨hac, hbc⟩⟩⟩
  omega

private theorem m22_nonlocal_excludes_trichotomy {T : Type*} [Fintype T]
    (K : SimpleGraph T) [DecidableRel K.Adj]
    (hOrder : Fintype.card T = 60) (hDegree : K.IsRegularOfDegree 12)
    (hTriangleFree : ∀ {a b c}, K.Adj a b → K.Adj a c → ¬ K.Adj b c) :
    ¬ (K = ⊤ ∨ K = ⊥ ∨ HasRankThreeAutAction K) := by
  classical
  intro hCases
  have hPositive : 0 < Fintype.card T := by omega
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp hPositive
  have hNeighbours : Fintype.card (K.neighborSet a) = 12 := by
    rw [K.card_neighborSet_eq_degree, hDegree.degree_eq]
  obtain ⟨b, c, hbc⟩ := Fintype.exists_pair_of_one_lt_card (α := K.neighborSet a) (by omega)
  have hDistinct : b.val ≠ c.val := fun h => hbc (Subtype.ext h)
  have hNonedge := hTriangleFree b.property c.property
  rcases hCases with hComplete | hEmpty | hRank
  · apply hNonedge
    exact (congrArg (fun F : SimpleGraph T => F.Adj b.val c.val) hComplete).mpr
      ((SimpleGraph.top_adj _ _).mpr hDistinct)
  · have hAdj : (⊥ : SimpleGraph T).Adj a b.val := hEmpty ▸ b.property
    exact hAdj
  · obtain ⟨d, l, m, hSRG⟩ := rankThree_isSRG K hRank
    have hd : d = 12 := (hSRG.regular a).symm.trans (hDegree a)
    have hLambda : l = 0 := by
      by_contra hNonzero
      have hPos : 0 < Fintype.card (K.commonNeighbors a b.val) := by
        rw [hSRG.of_adj a b.val b.property]
        omega
      obtain ⟨t⟩ := Fintype.card_pos_iff.mp hPos
      exact hTriangleFree b.property t.property.1 t.property.2
    have hParameters := SimpleGraph.IsSRGWith.param_eq K hSRG hPositive
    rw [hd, hOrder, hLambda] at hParameters
    omega

/-- The M₂₂ exclusion takes the rank-three action and the point stabilizer
order as graph-specific inputs. -/
theorem mathieuTwentyTwo_not_eppa_embedding {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (h : H.IsSRGWith 77 16 0 4) (hRank : HasRankThreeAutAction H)
    (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 11520)
    (e : V ↪ W) (hLarge : 39 ≤ Nat.card V) :
    ¬ IsEPPAEmbedding G H e := by
  classical
  intro heppa
  let _ : Fintype V := Fintype.ofFinite V
  have hV : 39 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hLarge
  have _ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let root : V := Classical.choice inferInstance
  let T := {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x}
  let N := {x : V // root ≠ x ∧ ¬ G.Adj root x}
  let K := nonlocalGraph H (e root)
  have hProfile : HasRegularProfile K (60, 12) :=
    constituentGraph_profile H ⟨77, 16, 0, 4⟩ h (e root) true
  have hOrder : Fintype.card T = 60 := by
    rw [← Nat.card_eq_fintype_card]
    exact hProfile.1
  have hDegree : K.IsRegularOfDegree 12 := by
    intro x
    rw [← K.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hProfile.2 x
  have hTriangleFree {a b c : T} (hab : K.Adj a b) (hac : K.Adj a c) : ¬ K.Adj b c :=
    triangleFree_of_srg H h hab hac
  have hN : Fintype.card N ≤ 30 := by
    by_contra! hStrict
    have hLocalEPPA := nonlocal_eppa G H e heppa root
    have hCases := transitive_eppa_at_most_double_clique_empty_or_rank_three (V := N) (W := T)
      (nonlocalGraph G root) K _ hLocalEPPA (nonlocalGraph_transitive H hRank (e root))
      (by omega) (by intro heq; omega)
    exact m22_nonlocal_excludes_trichotomy K hOrder hDegree hTriangleFree hCases
  have hSplit : Fintype.card V =
      1 + Fintype.card (G.neighborSet root) + Fintype.card N := by
    simpa only [Nat.card_eq_fintype_card] using order_eq_one_add_subconstituent_orders G root
  have hLocalOrder : 8 ≤ Nat.card (G.neighborSet root) := by
    rw [Nat.card_eq_fintype_card]
    omega
  have hIndependent : localGraph G root = ⊥ := by
    ext a b
    change G.Adj a.val b.val ↔ False
    constructor
    · intro hab
      exact triangleFree_of_srg H h ((heppa.1 root a.val).mp a.property)
        ((heppa.1 root b.val).mp b.property) ((heppa.1 a.val b.val).mp hab)
    · exact False.elim
  have hDiv := factorial_dvd_rootStabilizer_card_of_homogeneous_subset
    G H e heppa root (G.neighborSet root) (G.loopless.irrefl root)
    (fun _ hx _ hy => iff_of_true hx hy) (Or.inr hIndependent) hLocalOrder
  rw [hStabilizer (e root)] at hDiv
  exact (show ¬ Nat.factorial 8 ∣ 11520 by decide) hDiv

/-- Maximum-order formulation of the M₂₂ exclusion. -/
theorem mathieuTwentyTwo_maxEppaOrder_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h : H.IsSRGWith 77 16 0 4)
    (hRank : HasRankThreeAutAction H)
    (hStabilizer : ∀ r, Nat.card (pointwiseGraphStabilizer H {r}) = 11520) :
    maxEppaOrder H ≤ 38 := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained H
  by_contra! hLarge
  exact mathieuTwentyTwo_not_eppa_embedding (H.induce S) H h hRank hStabilizer
    (Function.Embedding.subtype S) (by omega) heppa

end EPPAIII.Primitive
