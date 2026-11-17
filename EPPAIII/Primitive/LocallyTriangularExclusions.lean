import EPPAIII.EPPA.HostRelabel
import EPPAIII.Primitive.AffineLineExclusionFromSubdegrees
import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.TriangularEmbedding
import EPPAIII.Primitive.TriangularRoot

/-!
# The locally triangular hosts of orders 256 and 2048

A degree bound from the triangular EPPA criterion and Mantel’s theorem
leaves many selected common nonneighbours of a small set of anchors.
Successive stabilizer indices place a lower bound on the order of a
host nonedge stabilizer.
-/

namespace EPPAIII.Primitive

private theorem card_mul_stabilizer_le_of_common_nonneighbours {V W : Type*}
    [Fintype V] [Finite W] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (U S : Finset V)
    (hOut : ∀ x ∈ S, x ∉ U)
    (hNonadj : ∀ x ∈ S, ∀ u ∈ U, ¬ G.Adj x u)
    {x : V} (hx : x ∈ S) :
    S.card * Nat.card (hostPointwiseStabilizer H (e '' (↑(insert x U) : Set V))) ≤
      Nat.card (hostPointwiseStabilizer H (e '' (↑U : Set V))) := by
  classical
  let Q := hostPointwiseStabilizer H (e '' (↑U : Set V))
  let O := MulAction.orbit Q (e x)
  let R := MulAction.stabilizer Q (e x)
  let T := hostPointwiseStabilizer H (e '' (↑(insert x U) : Set V))
  have hMove (y : S) : e y.val ∈ O := by
    obtain ⟨q, hq, hMap, hFix⟩ := eppa_same_profile_extension G H e heppa U x y.val
      (hOut x hx) (hOut y.val y.property) (fun u hu =>
        iff_of_false (hNonadj x hx u hu) (hNonadj y.val y.property u hu))
    refine ⟨⟨q, hq, ?_⟩, hMap⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hFix u hu
  let encode : S → O := fun y => ⟨e y.val, hMove y⟩
  have hEncode : Function.Injective encode := by
    intro a b hab
    exact Subtype.ext (e.injective (congrArg Subtype.val hab))
  have hOrbit := Nat.card_le_card_of_injective encode hEncode
  rw [Nat.card_eq_fintype_card (α := ↥S), Fintype.card_coe] at hOrbit
  have hEquiv : R ≃ T :=
    { toFun := fun q => ⟨q.val.val, q.val.property.1, by
        rintro _ ⟨u, hu, rfl⟩
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact q.property
        · exact q.val.property.2 (e u) ⟨u, hu, rfl⟩⟩
      invFun := fun q => ⟨⟨q.val, q.property.1, by
          rintro _ ⟨u, hu, rfl⟩
          exact q.property.2 (e u) ⟨u, Finset.mem_insert_of_mem hu, rfl⟩⟩,
        q.property.2 (e x) ⟨x, Finset.mem_insert_self x U, rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hProduct : Nat.card O * Nat.card R = Nat.card Q := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup Q (e x))
  change S.card * Nat.card T ≤ Nat.card Q
  rw [← Nat.card_congr hEquiv, ← hProduct]
  exact Nat.mul_le_mul_right _ hOrbit

private theorem exists_common_nonneighbour_stabilizer_descent {V W : Type*}
    [Fintype V] [Finite W] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) {k : ℕ} (hDegree : ∀ x, G.degree x ≤ k)
    (U : Finset V) {m : ℕ} (hm : 0 < m) (hmU : m + (k + 1) * U.card ≤ Fintype.card V) :
    ∃ x ∉ U, (∀ u ∈ U, ¬ G.Adj x u) ∧
      m * Nat.card (hostPointwiseStabilizer H (e '' (↑(insert x U) : Set V))) ≤
        Nat.card (hostPointwiseStabilizer H (e '' (↑U : Set V))) := by
  let N := U.biUnion (fun v => G.neighborFinset v)
  let S := (U ∪ N)ᶜ
  have hN : N.card ≤ U.card * k :=
    Finset.card_biUnion_le_card_mul U (fun v => G.neighborFinset v) k (by
      intro u _
      simpa only [G.card_neighborFinset_eq_degree] using hDegree u)
  have hTotal := Finset.card_union_le U N
  have hCompl := Finset.card_compl_add_card (U ∪ N)
  have hS : m ≤ S.card := by
    change m ≤ (U ∪ N)ᶜ.card
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm k] at hmU
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hm.trans_le hS)
  have hOut (y : V) (hy : y ∈ S) : y ∉ U := fun h =>
    (Finset.mem_compl.mp hy) (Finset.mem_union_left N h)
  have hNonadj (y : V) (hy : y ∈ S) (u : V) (hu : u ∈ U) : ¬ G.Adj y u :=
    fun h => (Finset.mem_compl.mp hy) (Finset.mem_union_right U
      (Finset.mem_biUnion.mpr ⟨u, hu, G.mem_neighborFinset u y |>.mpr h.symm⟩))
  exact ⟨x, hOut x hx, hNonadj x hx,
    (Nat.mul_le_mul_right _ hS).trans
      (card_mul_stabilizer_le_of_common_nonneighbours G H e heppa U S hOut hNonadj hx)⟩

private theorem selected_degree_le_of_locally_triangular {V W : Type*}
    [Fintype V] [Fintype W] (G : SimpleGraph V) [DecidableRel G.Adj] (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) {m : ℕ} (hm : 5 ≤ m)
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph (Fin m))) :
    ∀ x, G.degree x ≤ max (m ^ 2 / 4) (m.choose 2 / 2) := by
  classical
  intro x
  by_contra! hLarge
  obtain ⟨iso⟩ := hLocal (e x)
  have hOrder : Fintype.card (TwoSet (Fin m)) = m.choose 2 := by
    rw [triangularGraph_card, Fintype.card_fin]
  let d : G.neighborSet x ↪ H.neighborSet (e x) :=
    restrictEmbedding e (fun y hy => (heppa.1 x y).mp hy)
  let f : G.neighborSet x ↪ TwoSet (Fin m) := d.trans iso.toEquiv.toEmbedding
  have hEp : IsEPPAEmbedding (localGraph G x) (triangularGraph (Fin m)) f :=
    eppa_relabel_host (localGraph G x) d (local_eppa G H e heppa x) iso
  have hDegree := G.card_neighborSet_eq_degree x
  have hHalf : Fintype.card (TwoSet (Fin m)) ≤ 2 * Fintype.card (G.neighborSet x) := by
    have hB := le_max_right (m ^ 2 / 4) (m.choose 2 / 2)
    omega
  have hFree := (triangularGraph_eppa_iff_triangleFreeRange _ f hEp.1
    (by simpa using hm) hHalf).mp hEp
  have hMantel := card_triangularSelection_le_mantel (Set.range f) hFree
  have hRange := Fintype.card_congr (Equiv.ofInjective f f.injective)
  rw [Fintype.card_fin] at hMantel
  have hB := le_max_left (m ^ 2 / 4) (m.choose 2 / 2)
  omega

private theorem locallyTriangular_nonedge_stabilizer_mul {W : Type*} [Fintype W]
    (H : SimpleGraph W) {m : ℕ}
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph (Fin m)))
    (hTrans : ∀ x y z, x ≠ y → x ≠ z → ¬ H.Adj x y → ¬ H.Adj x z →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z)
    (x y : W) (hxy : x ≠ y) (hNonedge : ¬ H.Adj x y) :
    Nat.card (hostPointwiseStabilizer H {x, y}) * (Fintype.card W - 1 - m.choose 2) =
      Nat.card (hostPointwiseStabilizer H {x}) := by
  classical
  have hCount := hostPairStabilizer_card_mul_subdegree H x y hxy
    (fun z hz hStatus => hTrans x y z hxy hz hNonedge (hNonedge ∘ hStatus.mpr))
  have hEq (z : W) : (H.Adj x y ↔ H.Adj x z) ↔ ¬ H.Adj x z := by
    exact ⟨fun h => hNonedge ∘ h.mpr, iff_of_false hNonedge⟩
  let subtypeEquiv :
      {z : W // x ≠ z ∧ (H.Adj x y ↔ H.Adj x z)} ≃
        {z : W // x ≠ z ∧ ¬ H.Adj x z} :=
    Equiv.subtypeEquivRight fun z => and_congr Iff.rfl (hEq z)
  obtain ⟨iso⟩ := hLocal x
  have hDeg : Nat.card (H.neighborSet x) = m.choose 2 := by
    rw [Nat.card_congr iso.toEquiv, Nat.card_eq_fintype_card, triangularGraph_card,
      Fintype.card_fin]
  have hSplit := order_eq_one_add_subconstituent_orders H x
  rw [Nat.card_eq_fintype_card, hDeg] at hSplit
  rw [Nat.card_congr subtypeEquiv] at hCount
  have hSubdegree : Fintype.card W - 1 - m.choose 2 = Nat.card {z : W // x ≠ z ∧ ¬ H.Adj x z} := by
    omega
  rwa [hSubdegree]

/-- The locally `T(10)` example has no EPPA base of order at least 128.
The graph-specific inputs give the described model and the action on its
nonedges, and bound its point stabilizers by the order of `S₁₀`. -/
theorem locallyTriangular_order256_maxEppaOrder_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hOrder : Fintype.card W = 256)
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph (Fin 10)))
    (hPoint : ∀ r, Nat.card (hostPointwiseStabilizer H {r}) ≤ 3628800)
    (hTrans : ∀ x y z, x ≠ y → x ≠ z → ¬ H.Adj x y → ¬ H.Adj x z →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z) :
    maxEppaOrder H ≤ 127 := by
  classical
  by_contra! hLarge
  obtain ⟨A, hA, heppa⟩ := maxEppaOrder_attained H
  let G := H.induce A
  let e : A ↪ W := Function.Embedding.subtype _
  have hCard : 128 ≤ Fintype.card A := by
    rw [← Nat.card_eq_fintype_card, hA]
    omega
  have hDegree : ∀ x, G.degree x ≤ 25 :=
    selected_degree_le_of_locally_triangular G H e heppa (by decide) hLocal
  have hDescent := exists_common_nonneighbour_stabilizer_descent G H e heppa hDegree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card A by omega)
  obtain ⟨w, hw, hvw, _⟩ := hDescent {v} (m := 102) (by decide) (by simpa using hCard)
  have hNe : w ≠ v := by simpa using hw
  have hNonadj : ¬ H.Adj (e w) (e v) := heppa.1 w v |>.not.mp (hvw v (by simp))
  have hMul := locallyTriangular_nonedge_stabilizer_mul H hLocal hTrans
    (e w) (e v) (e.injective.ne hNe) hNonadj
  rw [hOrder] at hMul
  change Nat.card (hostPointwiseStabilizer H {e w, e v}) * 210 = _ at hMul
  have hPair : Nat.card (hostPointwiseStabilizer H {e w, e v}) ≤ 17280 := by
    have hPointBound := hPoint (e w)
    omega
  let U : Finset A := {w, v}
  have hU : U.card = 2 := by simp [U, hNe]
  have hFirst : Nat.card (hostPointwiseStabilizer H (e '' (↑U : Set A))) ≤ 17280 := by
    simpa [U, Set.image_insert_eq] using hPair
  obtain ⟨a, ha, _, hTwo⟩ := hDescent U (m := 76) (by decide) (by simpa [hU] using hCard)
  have hThree : (insert a U).card = 3 := by
    rw [Finset.card_insert_of_notMem ha, hU]
  obtain ⟨b, hb, _, hNext⟩ := hDescent (insert a U) (m := 50) (by decide)
    (by simpa [hThree] using hCard)
  have hFour : (insert b (insert a U)).card = 4 := by
    rw [Finset.card_insert_of_notMem hb, hThree]
  obtain ⟨c, _, _, hLast⟩ := hDescent (insert b (insert a U)) (m := 24) (by decide)
    (by simpa [hFour] using hCard)
  have hPositive : 0 < Nat.card (hostPointwiseStabilizer H (e '' (↑(insert c
      (insert b (insert a U))) : Set A))) := Nat.card_pos
  omega

/-- The locally `T(24)` example has no EPPA base of order at least 1024.
The graph-specific inputs give the described model and the action on its
nonedges, and bound its point stabilizers by the order of `M₂₄`. -/
theorem locallyTriangular_order2048_maxEppaOrder_le {W : Type*} [Fintype W]
    (H : SimpleGraph W) (hOrder : Fintype.card W = 2048)
    (hLocal : ∀ r, Nonempty (localGraph H r ≃g triangularGraph (Fin 24)))
    (hPoint : ∀ r, Nat.card (hostPointwiseStabilizer H {r}) ≤ 244823040)
    (hTrans : ∀ x y z, x ≠ y → x ≠ z → ¬ H.Adj x y → ¬ H.Adj x z →
      ∃ q : Equiv.Perm W, IsGraphAutomorphism H q ∧ q x = x ∧ q y = z) :
    maxEppaOrder H ≤ 1023 := by
  classical
  by_contra! hLarge
  obtain ⟨A, hA, heppa⟩ := maxEppaOrder_attained H
  let G := H.induce A
  let e : A ↪ W := Function.Embedding.subtype _
  have hCard : 1024 ≤ Fintype.card A := by
    rw [← Nat.card_eq_fintype_card, hA]
    omega
  have hDegree : ∀ x, G.degree x ≤ 144 :=
    selected_degree_le_of_locally_triangular G H e heppa (by decide) hLocal
  have hDescent := exists_common_nonneighbour_stabilizer_descent G H e heppa hDegree
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card A by omega)
  obtain ⟨w, hw, hvw, _⟩ := hDescent {v} (m := 879) (by decide) (by simpa using hCard)
  have hNe : w ≠ v := by simpa using hw
  have hNonadj : ¬ H.Adj (e w) (e v) := heppa.1 w v |>.not.mp (hvw v (by simp))
  have hMul := locallyTriangular_nonedge_stabilizer_mul H hLocal hTrans
    (e w) (e v) (e.injective.ne hNe) hNonadj
  rw [hOrder] at hMul
  change Nat.card (hostPointwiseStabilizer H {e w, e v}) * 1771 = _ at hMul
  have hPair : Nat.card (hostPointwiseStabilizer H {e w, e v}) ≤ 138240 := by
    have hPointBound := hPoint (e w)
    omega
  let U : Finset A := {w, v}
  have hU : U.card = 2 := by simp [U, hNe]
  have hFirst : Nat.card (hostPointwiseStabilizer H (e '' (↑U : Set A))) ≤ 138240 := by
    simpa [U, Set.image_insert_eq] using hPair
  obtain ⟨a, ha, _, hTwo⟩ := hDescent U (m := 734) (by decide) (by simpa [hU] using hCard)
  have hThree : (insert a U).card = 3 := by
    rw [Finset.card_insert_of_notMem ha, hU]
  obtain ⟨b, _, _, hNext⟩ := hDescent (insert a U) (m := 589) (by decide)
    (by simpa [hThree] using hCard)
  have hPositive : 0 < Nat.card (hostPointwiseStabilizer H (e '' (↑(insert b
      (insert a U)) : Set A))) := Nat.card_pos
  omega

end EPPAIII.Primitive
