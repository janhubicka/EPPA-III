import EPPAIII.Primitive.AffineMatchingExclusion
import EPPAIII.Primitive.PolarRankTwoConstituent

/-! # The rank-two symplectic graph over the field of order four -/

namespace EPPAIII.Primitive

open SimpleGraph

private abbrev LocalVertex := Fin 5 × Fin 4

private def occupiedRow (S : Finset LocalVertex) (i : Fin 5) : Finset LocalVertex :=
  S.filter (fun x => x.1 = i)

private def availableRows (a : Fin 5 → ℕ) (i j : Fin 5) (width : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j ∧ width ≤ a k)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 10000000 in
private theorem row_pattern (a : Fin 5 → Fin 5) (hSum : 11 ≤ ∑ i, (a i).val) :
    (∃ i, 2 ≤ (a i).val ∧
      2 ≤ (availableRows (fun k => (a k).val) i i 3).card) ∨
    (∃ i j, i ≠ j ∧ 1 ≤ (a i).val ∧ 1 ≤ (a j).val ∧
      2 ≤ (availableRows (fun k => (a k).val) i j 4).card) ∨
    (∃ i j, i ≠ j ∧ 1 ≤ (a i).val ∧ 1 ≤ (a j).val ∧
      3 ≤ (availableRows (fun k => (a k).val) i j 2).card) := by
  revert a
  -- The 3125 occupancy vectors are small. The three cases use just the row sizes.
  decide

private theorem card_occupiedRow_le (S : Finset LocalVertex) (i : Fin 5) :
    (occupiedRow S i).card ≤ 4 := by
  let e : (↑(occupiedRow S i) : Set LocalVertex) ↪ Fin 4 :=
    ⟨fun w => w.val.2, fun w z h => by
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp w.property).2.trans (Finset.mem_filter.mp z.property).2.symm
      · exact h⟩
  simpa using Fintype.card_le_of_embedding e

private theorem card_automorphisms_dvd_three_point_stabilizer
    {U V W : Type*} [Finite V] [Finite W] {J : SimpleGraph U}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (a b : G.neighborSet root)
    (f : J ↪g localGraph G root)
    (ha : ∀ x, a ≠ f x ∧ ¬ (localGraph G root).Adj a (f x))
    (hb : ∀ x, b ≠ f x ∧ ¬ (localGraph G root).Adj b (f x)) :
    Nat.card (graphAutomorphisms J) ∣ Nat.card (pointwiseGraphStabilizer H {e root, e a.val, e b.val}) := by
  classical
  let inclusion : localGraph G root ↪g G :=
    { toEmbedding := Function.Embedding.subtype _
      map_rel_iff' := Iff.rfl }
  let g := inclusion.comp f
  let S := Set.range g
  let D := ({root, a.val, b.val} : Finset V)
  have hOutside : ∀ u ∈ D, u ∉ S := by
    intro u hu
    rintro ⟨x, hx⟩
    rcases (show u = root ∨ u = a.val ∨ u = b.val by simpa [D] using hu) with rfl | rfl | rfl
    · exact (f x).property.ne hx.symm
    · exact (ha x).1 (Subtype.ext hx.symm)
    · exact (hb x).1 (Subtype.ext hx.symm)
  have hConst : ∀ p : graphAutomorphisms (G.induce S), ∀ u ∈ D, ∀ x : S,
      G.Adj u x.val ↔ G.Adj u (p.val x).val := by
    intro p u hu x
    obtain ⟨y, hy⟩ := x.property
    obtain ⟨z, hz⟩ := (p.val x).property
    rcases (show u = root ∨ u = a.val ∨ u = b.val by simpa [D] using hu) with rfl | rfl | rfl
    · exact iff_of_true (hy ▸ (f y).property) (hz ▸ (f z).property)
    · exact iff_of_false (hy ▸ (ha y).2) (hz ▸ (ha z).2)
    · exact iff_of_false (hy ▸ (hb y).2) (hz ▸ (hb z).2)
  have hSurj := restrictToSelected_surjective G H e heppa S D hOutside hConst
  have hImage : e '' (↑D : Set V) = {e root, e a.val, e b.val} := by simp [D]
  rw [card_automorphisms_of_iso g.isoInduceRange, ← hImage]
  exact (Subgroup.card_dvd_of_surjective hSurj).trans
    (setwiseGraphStabilizer H (e '' (↑D : Set V))
      (Set.range ((Function.Embedding.subtype (· ∈ S)).trans e))).card_subgroup_dvd_card

private theorem no_pattern_for_selected_local
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (hTriple : ∀ u v, u ≠ v → H.Adj (e root) u → H.Adj (e root) v →
      Nat.card (pointwiseGraphStabilizer H {e root, u, v}) = if H.Adj u v then 384 else 72)
    {S : Finset LocalVertex}
    (back : (cliqueUnion 5 4).induce (↑S : Set _) ↪g localGraph G root)
    {components width : ℕ} (positive : 0 < width) {a b : (↑S : Set LocalVertex)}
    (hne : a ≠ b)
    (hSize : components ≤ (availableRows (fun k => (occupiedRow S k).card) a.val.1 b.val.1 width).card)
    (hFail : ¬ components.factorial * width.factorial ^ components ∣
      (if a.val.1 = b.val.1 then 384 else 72)) : False := by
  classical
  let I := availableRows (fun k => (occupiedRow S k).card) a.val.1 b.val.1 width
  obtain ⟨rows : Fin components ↪ (↑I : Set (Fin 5))⟩ :=
    Function.Embedding.nonempty_of_card_le (α := Fin components) (β := (↑I : Set (Fin 5))) (by simpa [I] using hSize)
  have hRow (i : Fin components) :
      (rows i).val ≠ a.val.1 ∧ (rows i).val ≠ b.val.1 ∧
      width ≤ (occupiedRow S (rows i).val).card := (Finset.mem_filter.mp (rows i).property).2
  have hCoord (i : Fin components) :
      Nonempty (Fin width ↪ (↑(occupiedRow S (rows i).val) : Set LocalVertex)) :=
    Function.Embedding.nonempty_of_card_le (α := Fin width)
      (β := (↑(occupiedRow S (rows i).val) : Set LocalVertex)) (by simpa using (hRow i).2.2)
  let coord (i : Fin components) := Classical.choice (hCoord i)
  let f (x : Fin components × Fin width) : (↑S : Set LocalVertex) :=
    ⟨(coord x.1 x.2).val, (Finset.mem_filter.mp (coord x.1 x.2).property).1⟩
  have hFirst (x : Fin components × Fin width) : (f x).val.1 = (rows x.1).val :=
    (Finset.mem_filter.mp (coord x.1 x.2).property).2
  have hCol (i : Fin components) {u v : Fin width} (h : (f (i,u)).val.2 = (f (i,v)).val.2) :
      u = v := (coord i).injective (Subtype.ext (Prod.ext ((hFirst (i,u)).trans (hFirst (i,v)).symm) h))
  have hRowEq (x y : Fin components × Fin width) :
      (f x).val.1 = (f y).val.1 ↔ x.1 = y.1 := by
    rw [hFirst, hFirst]
    exact ⟨fun h => rows.injective (Subtype.ext h), fun h => congrArg (fun i => (rows i).val) h⟩
  let chart : cliqueUnion components width ↪g (cliqueUnion 5 4).induce (↑S : Set _) :=
    ⟨⟨f, by
      rintro ⟨i,u⟩ ⟨j,v⟩ h
      have hij : i = j := (hRowEq (i,u) (j,v)).mp (congrArg (fun x => x.val.1) h)
      subst j
      exact Prod.ext rfl (hCol i (congrArg (fun x => x.val.2) h))⟩, by
      rintro ⟨i,u⟩ ⟨j,v⟩
      change (f (i,u)).val.1 = (f (j,v)).val.1 ∧ (f (i,u)).val.2 ≠ (f (j,v)).val.2 ↔ i = j ∧ u ≠ v
      rw [hRowEq]
      by_cases hij : i = j
      · subst j
        simpa only [true_and] using not_congr ⟨hCol i, (fun h => congrArg (fun k => (f (i,k)).val.2) h)⟩
      · simp [hij]⟩
  have hDisjointA (x : Fin components × Fin width) : a.val.1 ≠ (f x).val.1 := by
    rw [hFirst]; exact (hRow x.1).1.symm
  have hDisjointB (x : Fin components × Fin width) : b.val.1 ≠ (f x).val.1 := by
    rw [hFirst]; exact (hRow x.1).2.1.symm
  have hDiv := card_automorphisms_dvd_three_point_stabilizer G H e heppa root
    (back a) (back b) (back.comp chart)
    (fun x => ⟨fun h => hDisjointA x (congrArg (fun y => y.val.1) (back.injective h)),
      fun h => hDisjointA x (back.map_rel_iff.mp h).1⟩)
    (fun x => ⟨fun h => hDisjointB x (congrArg (fun y => y.val.1) (back.injective h)),
      fun h => hDisjointB x (back.map_rel_iff.mp h).1⟩)
  have hHostAdj : H.Adj (e (back a).val) (e (back b).val) ↔ a.val.1 = b.val.1 := by
    rw [← heppa.1]
    change (localGraph G root).Adj (back a) (back b) ↔ _
    rw [back.map_rel_iff]
    change a.val.1 = b.val.1 ∧ a.val.2 ≠ b.val.2 ↔ _
    refine ⟨And.left, fun h => ⟨h, fun hc => hne (Subtype.ext (Prod.ext h hc))⟩⟩
  rw [card_automorphisms_cliqueUnion positive,
    hTriple _ _ (fun h => hne (back.injective (Subtype.ext (e.injective h))))
      ((heppa.1 _ _).mp (back a).property) ((heppa.1 _ _).mp (back b).property)] at hDiv
  by_cases h : a.val.1 = b.val.1
  · exact hFail (by simpa only [ite_eq_left h, ite_eq_left (hHostAdj.mpr h)] using hDiv)
  · exact hFail (by simpa only [ite_eq_right h, ite_eq_right (fun h' => h (hHostAdj.mp h'))] using hDiv)

private theorem select_anchors (S : Finset LocalVertex) (i j : Fin 5)
    (h : if i = j then 2 ≤ (occupiedRow S i).card else
      1 ≤ (occupiedRow S i).card ∧ 1 ≤ (occupiedRow S j).card) :
    ∃ a b : (↑S : Set LocalVertex), a ≠ b ∧ a.val.1 = i ∧ b.val.1 = j := by
  classical
  by_cases hRow : i = j
  · subst j
    rw [ite_eq_left rfl] at h
    obtain ⟨f : Fin 2 ↪ (↑(occupiedRow S i) : Set LocalVertex)⟩ :=
      Function.Embedding.nonempty_of_card_le (α := Fin 2)
        (β := (↑(occupiedRow S i) : Set LocalVertex)) (by simpa using h)
    let a := Finset.mem_filter.mp (f 0).property
    let b := Finset.mem_filter.mp (f 1).property
    exact ⟨⟨(f 0).val, a.1⟩, ⟨(f 1).val, b.1⟩,
      fun h' => (by decide : (0 : Fin 2) ≠ 1) (f.injective (Subtype.ext (congrArg (fun x : (↑S : Set LocalVertex) => x.val) h'))),
      a.2, b.2⟩
  · rw [ite_eq_right hRow] at h
    obtain ⟨a, ha⟩ := Finset.card_pos.mp h.1
    obtain ⟨b, hb⟩ := Finset.card_pos.mp h.2
    obtain ⟨haS, haI⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbS, hbJ⟩ := Finset.mem_filter.mp hb
    exact ⟨⟨a,haS⟩, ⟨b,hbS⟩, fun h' => hRow (haI.symm.trans ((congrArg (fun x => x.val.1) h').trans hbJ)), haI, hbJ⟩

/-- The local section arguments for (5K_4) leave at most ten selected vertices. -/
theorem symplecticFourFour_selected_local_le_ten
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (φ : localGraph H (e root) ≃g cliqueUnion 5 4)
    (hTriple : ∀ u v, u ≠ v → H.Adj (e root) u → H.Adj (e root) v →
      Nat.card (pointwiseGraphStabilizer H {e root, u, v}) = if H.Adj u v then 384 else 72) :
    Nat.card (G.neighborSet root) ≤ 10 := by
  classical
  let := Fintype.ofFinite V
  by_contra! hSelected
  let η : localGraph G root ↪g localGraph H (e root) :=
    { toEmbedding := restrictEmbedding e (fun x hx => (heppa.1 root x).mp hx)
      map_rel_iff' := fun {_ _} => (heppa.1 _ _).symm }
  let q := φ.toEmbedding.comp η
  let S : Finset LocalVertex := Finset.univ.map q.toEmbedding
  have hS : 11 ≤ S.card := by
    rw [Finset.card_map, Finset.card_univ]
    rw [Nat.card_eq_fintype_card] at hSelected
    omega
  have hrange : Set.range q = (↑S : Set _) := by
    ext x
    simp [S]
  let back : (cliqueUnion 5 4).induce (↑S : Set _) ↪g localGraph G root :=
    (hrange ▸ q.isoInduceRange).symm.toEmbedding
  let a (i : Fin 5) : Fin 5 := ⟨(occupiedRow S i).card, Nat.lt_succ_of_le (card_occupiedRow_le S i)⟩
  have hSum : 11 ≤ ∑ i, (a i).val := by
    change 11 ≤ ∑ i, (occupiedRow S i).card
    have hEq := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := S) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    exact hS.trans_eq hEq
  rcases row_pattern a hSum with ⟨i, hi, hRows⟩ | ⟨i, j, hij, hi, hj, hRows⟩ | ⟨i, j, hij, hi, hj, hRows⟩
  · obtain ⟨u, v, hne, hu, hv⟩ := select_anchors S i i (by rw [ite_eq_left (rfl : i = i)]; exact hi)
    refine no_pattern_for_selected_local G H e heppa root hTriple back (width := 3) (components := 2)
      (by decide) hne ?_ ?_
    · simpa only [hu, hv] using hRows
    · rw [hu, hv, ite_eq_left rfl]
      decide
  · obtain ⟨u, v, hne, hu, hv⟩ := select_anchors S i j (by rw [ite_eq_right hij]; exact ⟨hi, hj⟩)
    refine no_pattern_for_selected_local G H e heppa root hTriple back (width := 4) (components := 2)
      (by decide) hne ?_ ?_
    · simpa only [hu, hv] using hRows
    · rw [hu, hv, ite_eq_right hij]
      decide
  · obtain ⟨u, v, hne, hu, hv⟩ := select_anchors S i j (by rw [ite_eq_right hij]; exact ⟨hi, hj⟩)
    refine no_pattern_for_selected_local G H e heppa root hTriple back (width := 2) (components := 3)
      (by decide) hne ?_ ?_
    · simpa only [hu, hv] using hRows
    · rw [hu, hv, ite_eq_right hij]
      decide

/-- Exclude the canonical rank-two symplectic graph at field order four
using the local row argument and the nonlocal rank-two shape test. -/
theorem symplecticFourFour_not_eppa
    {V W : Type*} [Finite V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj] (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V)
    (hSRG : H.IsSRGWith 85 20 3 5)
    (φ : localGraph H (e root) ≃g cliqueUnion 5 4)
    (hTriple : ∀ u v, u ≠ v → H.Adj (e root) u → H.Adj (e root) v →
      Nat.card (pointwiseGraphStabilizer H {e root, u, v}) = if H.Adj u v then 384 else 72)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      let K := nonlocalGraph H (e root)
      (∃ s t, Nonempty (K ≃g cliqueUnion s t) ∨ Nonempty (K ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (K ≃g coverGraph s t X Y) ∨ Nonempty (K ≃g (coverGraph s t X Y)ᶜ))) :
    False := by
  classical
  have hLocalV := symplecticFourFour_selected_local_le_ten G H e heppa root φ hTriple
  have hLocalW : Nat.card (H.neighborSet (e root)) = 20 :=
    (Nat.card_congr φ.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  have hOrder : Nat.card W = 85 := Nat.card_eq_fintype_card.trans hSRG.card
  have hSplitW := order_eq_one_add_subconstituent_orders H (e root)
  have hSplitV := order_eq_one_add_subconstituent_orders G root
  have hLarge : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} := by omega
  have hRange : RankTwoPolarRange 4 4 := Or.inl ⟨by decide, by decide⟩
  obtain ⟨hC, hCC, hG, hCG⟩ :=
    polar_rankTwo_actual_second_constituent_excludes_forms H hRange hSRG (e root)
  rcases hShape hLarge with ⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩
  · rcases h with f | f
    · exact (hC s t).false (Classical.choice f)
    · exact (hCC s t).false (Classical.choice f)
  · rcases h with f | f
    · exact (hG s t X Y).false (Classical.choice f)
    · exact (hCG s t X Y).false (Classical.choice f)

end EPPAIII.Primitive
