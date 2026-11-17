import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.NeighbourhoodBound
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The Hoffman–Singleton exclusion

In a strongly regular graph with parameters `(50, 7, 0, 1)`, two selected
nonneighbours of a selected root have the same common neighbour with the
root. A partial automorphism fixing the root and one of those vertices
detects the adjacency of the other to that common neighbour.
-/

namespace EPPAIII.Primitive

/-- The obstruction uses the strongly regular parameters of the Hoffman–Singleton graph. -/
theorem hoffmanSingleton_not_eppa_embedding {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (h : H.IsSRGWith 50 7 0 1) (e : V ↪ W) (hLarge : 25 ≤ Nat.card V) :
    ¬ IsEPPAEmbedding G H e := by
  classical
  intro heppa
  let _ : Fintype V := Fintype.ofFinite V
  have hV : 25 ≤ Fintype.card V := by simpa only [Nat.card_eq_fintype_card] using hLarge
  have _ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let root : V := Classical.choice inferInstance
  let N := {x : V // root ≠ x ∧ ¬ G.Adj root x}
  have hLocalCount : Fintype.card (H.neighborSet (e root)) = 7 := by
    rw [H.card_neighborSet_eq_degree, h.regular.degree_eq]
  let localMap : G.neighborSet root ↪ H.neighborSet (e root) :=
    restrictEmbedding e (fun x hx => (heppa.1 root x).mp hx)
  have hLocalLe := Fintype.card_le_of_embedding localMap
  have hSplit : Fintype.card V = 1 + Fintype.card (G.neighborSet root) + Fintype.card N := by
    simpa only [Nat.card_eq_fintype_card] using order_eq_one_add_subconstituent_orders G root
  have hN : 17 ≤ Fintype.card N := by omega
  have hCommonCard (x : N) : Fintype.card (H.commonNeighbors (e root) (e x.val)) = 1 :=
    h.of_not_adj (fun heq => x.property.1 (e.injective heq))
      (fun hadj => x.property.2 ((heppa.1 root x.val).mpr hadj))
  let common (x : N) : H.commonNeighbors (e root) (e x.val) :=
    Classical.choice (Fintype.card_pos_iff.mp (by rw [hCommonCard x]; omega))
  let neighbour (x : N) : H.neighborSet (e root) :=
    ⟨(common x).val, (H.mem_commonNeighbors.mp (common x).property).1⟩
  obtain ⟨x, y, hxy, hSame⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt neighbour (by omega)
  let n : W := (common x).val
  have hCommonX : H.Adj (e root) n ∧ H.Adj (e x.val) n :=
    H.mem_commonNeighbors.mp (common x).property
  have hCommonY : H.Adj (e y.val) n := by
    have heq : n = (common y).val :=
      congrArg (fun w : H.neighborSet (e root) => w.val) hSame
    rw [heq]
    exact (H.mem_commonNeighbors.mp (common y).property).2
  have hNotXY : ¬ G.Adj y.val x.val := by
    intro hadj
    have hZero := h.of_adj _ _ ((heppa.1 y.val x.val).mp hadj)
    have hPos : 0 < Fintype.card (H.commonNeighbors (e y.val) (e x.val)) :=
      Fintype.card_pos_iff.mpr ⟨⟨n, H.mem_commonNeighbors.mpr ⟨hCommonY, hCommonX.2⟩⟩⟩
    omega
  let forbidden : Finset W :=
    insert (e x.val) (H.neighborFinset (e x.val) ∪ H.neighborFinset n)
  have hForbidden : forbidden.card ≤ 15 := by
    calc
      forbidden.card ≤ (H.neighborFinset (e x.val) ∪ H.neighborFinset n).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ (H.neighborFinset (e x.val)).card + (H.neighborFinset n).card + 1 :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ = 15 := by simp only [H.card_neighborFinset_eq_degree, h.regular.degree_eq]
  have hOutside : ∃ z : N, e z.val ∉ forbidden := by
    by_contra! hAll
    let intoForbidden (z : N) : ↥forbidden := ⟨e z.val, hAll z⟩
    have hLe := Fintype.card_le_of_injective intoForbidden
      (fun _ _ hEq => Subtype.ext (e.injective (congrArg Subtype.val hEq)))
    rw [Fintype.card_coe] at hLe
    omega
  obtain ⟨z, hz⟩ := hOutside
  have hZx : z.val ≠ x.val := by
    intro heq
    exact hz (heq ▸ Finset.mem_insert_self _ _)
  have hZnotX : ¬ G.Adj z.val x.val := by
    intro hadj
    exact hz (Finset.mem_insert_of_mem (Finset.mem_union_left _
      ((H.mem_neighborFinset _ _).mpr ((heppa.1 z.val x.val).mp hadj).symm)))
  have hZnotN : ¬ H.Adj (e z.val) n := by
    intro hadj
    exact hz (Finset.mem_insert_of_mem (Finset.mem_union_right _
      ((H.mem_neighborFinset _ _).mpr hadj.symm)))
  have hYx : y.val ≠ x.val := fun hEq => hxy (Subtype.ext hEq.symm)
  have hSameProfile (u : V) (hu : u ∈ ({root, x.val} : Finset V)) :
      G.Adj y.val u ↔ G.Adj z.val u := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact iff_of_false (fun adj => y.property.2 adj.symm)
        (fun adj => z.property.2 adj.symm)
    · exact iff_of_false hNotXY hZnotX
  obtain ⟨q, hq, hMap, hFix⟩ := eppa_same_profile_extension G H e heppa
    {root, x.val} y.val z.val
    (by simp [Ne.symm y.property.1, hYx])
    (by simp [Ne.symm z.property.1, hZx]) hSameProfile
  have hRootFix := hFix root (by simp)
  have hXFix := hFix x.val (by simp)
  let image : H.commonNeighbors (e root) (e x.val) :=
    ⟨q n, H.mem_commonNeighbors.mpr
      ⟨hRootFix ▸ (hq (e root) n).mp hCommonX.1,
        hXFix ▸ (hq (e x.val) n).mp hCommonX.2⟩⟩
  have hNFix : q n = n := by
    have hUnique := Fintype.card_le_one_iff.mp (le_of_eq (hCommonCard x))
    exact congrArg Subtype.val (hUnique image (common x))
  exact hZnotN (hMap ▸ hNFix ▸ (hq (e y.val) n).mp hCommonY)

/-- The bound also applies to the maximum EPPA subgraph order of the host. -/
theorem hoffmanSingleton_maxEppaOrder_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h : H.IsSRGWith 50 7 0 1) :
    maxEppaOrder H ≤ 24 := by
  obtain ⟨S, hCard, heppa⟩ := maxEppaOrder_attained H
  by_contra! hLarge
  exact hoffmanSingleton_not_eppa_embedding (H.induce S) H h
    (Function.Embedding.subtype S) (by omega) heppa

end EPPAIII.Primitive
