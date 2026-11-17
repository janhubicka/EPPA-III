import EPPAIII.Primitive.LocalSections
import EPPAIII.Primitive.TriangularObstruction

/-! # The full automorphism group of a triangular graph -/

namespace EPPAIII.Primitive

private def triangularStar {V : Type*} [Fintype V] [DecidableEq V] (x : V) :
    Finset (TwoSet V) :=
  Finset.univ.filter fun a => x ∈ a.val

@[simp]
private theorem mem_triangularStar {V : Type*} [Fintype V] [DecidableEq V]
    {x : V} {a : TwoSet V} : a ∈ triangularStar x ↔ x ∈ a.val := by
  simp [triangularStar]

private theorem card_triangularStar {V : Type*} [Fintype V] [DecidableEq V] (x : V) :
    (triangularStar x).card = Fintype.card V - 1 := by
  let f : {y : V // y ≠ x} → triangularStar x :=
    fun y => ⟨triangularPair x y (Ne.symm y.property), by simp [triangularPair]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have hpair := congrArg (fun z : triangularStar x => z.val.val) hab
      have ha : a.val ∈ (triangularPair x b (Ne.symm b.property)).val := by
        change a.val ∈ ({x, b.val} : Finset V)
        rw [← show ({x, a.val} : Finset V) = {x, b.val} from hpair]
        simp
      simpa [triangularPair, a.property] using ha
    · intro a
      obtain ⟨y, hxy, hy⟩ := exists_triangularPair_of_mem (mem_triangularStar.mp a.property)
      exact ⟨⟨y, hxy.symm⟩, Subtype.ext hy.symm⟩
  rw [← Fintype.card_coe, ← Fintype.card_congr (Equiv.ofBijective f hf)]
  have hOne : Fintype.card {y : V // y = x} = 1 := Fintype.card_unique
  rw [Fintype.card_subtype_compl, hOne]

private theorem star_injective {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 3 ≤ Fintype.card V) : Function.Injective (triangularStar : V → _) := by
  intro x y hxy
  by_contra hne
  have hOutside : ∃ z : V, z ∉ ({x, y} : Finset V) := by
    by_contra! hAll
    have heq := Finset.eq_univ_of_forall hAll
    have hc := Finset.card_insert_le x ({y} : Finset V)
    rw [heq, Finset.card_univ, Finset.card_singleton] at hc
    omega
  obtain ⟨z, hz⟩ := hOutside
  have hxz : x ≠ z := fun h => hz (by simp [h])
  have hyz : y ≠ z := fun h => hz (by simp [h])
  have hmem : triangularPair x z hxz ∈ triangularStar x := by simp [triangularPair]
  rw [hxy, mem_triangularStar] at hmem
  exact hne ((show y = x from by simpa [triangularPair, hyz] using hmem).symm)

private theorem common_point_of_large_clique {V : Type*} [DecidableEq V]
    (S : Finset (TwoSet V)) (hS : 4 ≤ S.card)
    (hClique : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (triangularGraph V).Adj a b) :
    ∃ x, ∀ a ∈ S, x ∈ a.val := by
  have hTriangleFree : TriangleFreeEdges (S : Set (TwoSet V)) := by
    intro x y z hxy hxz hyz h₁ h₂ h₃
    change triangularPair x y hxy ∈ S at h₁
    change triangularPair x z hxz ∈ S at h₂
    change triangularPair y z hyz ∈ S at h₃
    let t : Finset (TwoSet V) :=
      {triangularPair x y hxy, triangularPair x z hxz, triangularPair y z hyz}
    have ht : t.card ≤ 3 := by
      calc
        _ ≤ ({triangularPair x z hxz, triangularPair y z hyz} : Finset _).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ (({triangularPair y z hyz} : Finset _).card + 1) + 1 :=
          Nat.add_le_add_right (Finset.card_insert_le _ _) _
        _ = 3 := by simp
    have hOutside : ∃ d ∈ S, d ∉ t := by
      by_contra! hSub
      have h := Finset.card_le_card (show S ⊆ t from hSub)
      omega
    obtain ⟨d, hd, hdt⟩ := hOutside
    obtain ⟨hd₁, hd₂, hd₃⟩ : d ≠ triangularPair x y hxy ∧
        d ≠ triangularPair x z hxz ∧ d ≠ triangularPair y z hyz := by
      simpa [t] using hdt
    exact no_fourth_for_root_triangle hxy hxz hyz d
      (hClique d hd _ h₁ hd₁) (hClique d hd _ h₂ hd₂) (hClique d hd _ h₃ hd₃)
  let e : S ↪ (S : Set (TwoSet V)) := ⟨fun a => ⟨a.val, a.property⟩,
    fun _ _ h => Subtype.ext (congrArg Subtype.val h)⟩
  have hBig : 1 < (Finset.univ : Finset S).card := by
    rw [Finset.card_univ, Fintype.card_coe]
    omega
  obtain ⟨x, hx⟩ := exists_common_point_of_triangularClique hTriangleFree e hBig
    (fun a _ b _ hab => hClique a a.property b b.property (fun h => hab (Subtype.ext h)))
  exact ⟨x, fun a ha => hx ⟨a, ha⟩ (Finset.mem_univ _)⟩

private theorem image_star_is_star {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 5 ≤ Fintype.card V) (p : graphAutomorphisms (triangularGraph V)) (x : V) :
    ∃ y, (triangularStar x).map p.val.toEmbedding = triangularStar y := by
  let S := (triangularStar x).map p.val.toEmbedding
  have hS : S.card = Fintype.card V - 1 := by
    simp [S, card_triangularStar]
  obtain ⟨y, hy⟩ := common_point_of_large_clique S (by omega) (by
    intro a ha b hb hab
    obtain ⟨a, haStar, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨b, hbStar, rfl⟩ := Finset.mem_map.mp hb
    exact (p.property a b).mp
      ⟨fun h => hab (congrArg p.val h), x, mem_triangularStar.mp haStar, mem_triangularStar.mp hbStar⟩)
  exact ⟨y, Finset.eq_of_subset_of_card_le (fun a ha => mem_triangularStar.mpr (hy a ha))
    (by rw [hS, card_triangularStar])⟩

/-- On at least five points a triangular-graph automorphism determines a
permutation of the stars, and the latter determines the automorphism. -/
theorem triangularGraph_automorphism_card_le {V : Type*} [Fintype V]
    (hV : 5 ≤ Fintype.card V) :
    Nat.card (graphAutomorphisms (triangularGraph V)) ≤ (Fintype.card V).factorial := by
  classical
  let f (p : graphAutomorphisms (triangularGraph V)) (x : V) :=
    (image_star_is_star hV p x).choose
  have hf (p : graphAutomorphisms (triangularGraph V)) (x : V) :
      (triangularStar x).map p.val.toEmbedding = triangularStar (f p x) :=
    (image_star_is_star hV p x).choose_spec
  have hInjective (p : graphAutomorphisms (triangularGraph V)) : Function.Injective (f p) := by
    intro a b h
    have hMap : (triangularStar a).map p.val.toEmbedding =
        (triangularStar b).map p.val.toEmbedding := (hf p a).trans (h ▸ (hf p b).symm)
    exact star_injective (by omega) (Finset.map_injective _ hMap)
  let F (p : graphAutomorphisms (triangularGraph V)) :=
    Equiv.ofBijective (f p) ⟨hInjective p, Finite.surjective_of_injective (hInjective p)⟩
  have hF : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    apply Equiv.ext
    intro e
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.property
    have hFa : f p a = f q a := congrArg (fun p : Equiv.Perm V => p a) hpq
    have hFb : f p b = f q b := congrArg (fun p : Equiv.Perm V => p b) hpq
    have hMem (r : graphAutomorphisms (triangularGraph V)) (x : V) (hx : x ∈ e.val) :
        f r x ∈ (r.val e).val := by
      apply mem_triangularStar.mp
      rw [← hf r x]
      exact Finset.mem_map.mpr ⟨e, mem_triangularStar.mpr hx, rfl⟩
    have hNe := (hInjective p).ne hab
    have hp := triangularPair_of_mem (hMem p a (by simp [he])) (hMem p b (by simp [he])) hNe
    have hq := triangularPair_of_mem (hFa ▸ hMem q a (by simp [he]))
      (hFb ▸ hMem q b (by simp [he])) hNe
    exact hp.trans hq.symm
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm] using
    (Nat.card_le_card_of_injective F hF)

end EPPAIII.Primitive
