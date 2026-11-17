import EPPAIII.Primitive.Triangular
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.FinCases

/-!
# The triangle obstruction in a fixed triangular embedding

When there are at least five points, a star of three edges extends to a clique
of order four in the triangular host. The three edges of a triangle do not.
An EPPA selection containing the second configuration therefore has degree at
most two on its underlying points.
-/

namespace EPPAIII.Primitive

open Finset
open scoped BigOperators

/-- The two-element set of distinct points `x` and `y`. -/
def triangularPair {V : Type*} [DecidableEq V] (x y : V) (hxy : x ≠ y) : TwoSet V :=
  ⟨{x, y}, by simp [hxy]⟩

@[simp] private theorem mem_pair {V : Type*} [DecidableEq V]
    (x y z : V) (hxy : x ≠ y) : z ∈ (triangularPair x y hxy).val ↔ z = x ∨ z = y := by
  simp [triangularPair]

/-- Two distinct points of a two-element set determine that set. -/
theorem triangularPair_of_mem {V : Type*} [DecidableEq V] {x y : V} {e : TwoSet V}
    (hx : x ∈ e.val) (hy : y ∈ e.val) (hxy : x ≠ y) : e = triangularPair x y hxy := by
  apply Subtype.ext
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rcases (mem_pair x y z hxy).mp hz with rfl | rfl
    · exact hx
    · exact hy
  · simp only [e.property, (triangularPair x y hxy).property, le_refl]

/-- A two-element set containing a point can be written as a pair beginning with that point. -/
theorem exists_triangularPair_of_mem {V : Type*} [DecidableEq V] {x : V} {e : TwoSet V}
    (hx : x ∈ e.val) : ∃ (y : V) (hxy : x ≠ y), e = triangularPair x y hxy := by
  obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp e.property
  rw [he, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab, triangularPair_of_mem (by simp [he]) (by simp [he]) hab⟩
  · exact ⟨a, hab.symm, triangularPair_of_mem (by simp [he]) (by simp [he]) hab.symm⟩

private theorem pair_ne_of_mem {V : Type*} [DecidableEq V] {a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triangularPair a b hab ≠ triangularPair a c hac := by
  intro hp
  have h : b ∈ (triangularPair a c hac).val := hp ▸ (mem_pair a b b hab).mpr (.inr rfl)
  rcases (mem_pair a c b hac).mp h with h | h
  · exact hab h.symm
  · exact hbc h

/-- The three edges of a root triangle form a clique in the triangular graph. -/
theorem root_pairs_adjacent {V : Type*} [DecidableEq V] {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (triangularGraph V).Adj (triangularPair x y hxy) (triangularPair x z hxz) ∧
      (triangularGraph V).Adj (triangularPair x y hxy) (triangularPair y z hyz) ∧
      (triangularGraph V).Adj (triangularPair x z hxz) (triangularPair y z hyz) := by
  have h₁ : triangularPair x y hxy ≠ triangularPair y z hyz := by
    intro h
    have hm : x ∈ (triangularPair y z hyz).val := h ▸ (mem_pair x y x hxy).mpr (.inl rfl)
    exact ((mem_pair y z x hyz).mp hm).elim hxy hxz
  have h₂ : triangularPair x z hxz ≠ triangularPair y z hyz := by
    intro h
    have hm : x ∈ (triangularPair y z hyz).val := h ▸ (mem_pair x z x hxz).mpr (.inl rfl)
    exact ((mem_pair y z x hyz).mp hm).elim hxy hxz
  exact ⟨⟨pair_ne_of_mem hxy hxz hyz, x, by simp, by simp⟩,
    ⟨h₁, y, by simp, by simp⟩, ⟨h₂, z, by simp, by simp⟩⟩

/-- The clique formed by a root triangle has no common neighbour in the triangular graph. -/
theorem no_fourth_for_root_triangle {V : Type*} [DecidableEq V]
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (e : TwoSet V)
    (he₁ : (triangularGraph V).Adj e (triangularPair x y hxy))
    (he₂ : (triangularGraph V).Adj e (triangularPair x z hxz))
    (he₃ : (triangularGraph V).Adj e (triangularPair y z hyz)) : False := by
  have h₁ : x ∈ e.val ∨ y ∈ e.val := by
    obtain ⟨_, a, ha, hp⟩ := he₁
    rcases (mem_pair x y a hxy).mp hp with rfl | rfl
    · exact .inl ha
    · exact .inr ha
  have h₂ : x ∈ e.val ∨ z ∈ e.val := by
    obtain ⟨_, a, ha, hp⟩ := he₂
    rcases (mem_pair x z a hxz).mp hp with rfl | rfl
    · exact .inl ha
    · exact .inr ha
  have h₃ : y ∈ e.val ∨ z ∈ e.val := by
    obtain ⟨_, a, ha, hp⟩ := he₃
    rcases (mem_pair y z a hyz).mp hp with rfl | rfl
    · exact .inl ha
    · exact .inr ha
  by_cases hx : x ∈ e.val
  · rcases h₃ with hy | hz
    · exact he₁.1 (triangularPair_of_mem hx hy hxy)
    · exact he₂.1 (triangularPair_of_mem hx hz hxz)
  · exact he₃.1 (triangularPair_of_mem (h₁.resolve_left hx) (h₂.resolve_left hx) hyz)

private theorem fourth_for_star {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 5 ≤ Fintype.card V) (x : V) (e₁ e₂ e₃ : TwoSet V)
    (hx₁ : x ∈ e₁.val) (hx₂ : x ∈ e₂.val) (hx₃ : x ∈ e₃.val) :
    ∃ e, (triangularGraph V).Adj e e₁ ∧ (triangularGraph V).Adj e e₂ ∧
      (triangularGraph V).Adj e e₃ := by
  obtain ⟨y₁, h₁, rfl⟩ := exists_triangularPair_of_mem hx₁
  obtain ⟨y₂, h₂, rfl⟩ := exists_triangularPair_of_mem hx₂
  obtain ⟨y₃, h₃, rfl⟩ := exists_triangularPair_of_mem hx₃
  let used : Finset V := {x, y₁, y₂, y₃}
  have hc : used.card ≤ 4 := by
    have h₁' := Finset.card_insert_le x ({y₁, y₂, y₃} : Finset V)
    have h₂' := Finset.card_insert_le y₁ ({y₂, y₃} : Finset V)
    have h₃' := Finset.card_insert_le y₂ ({y₃} : Finset V)
    have h₄' : ({y₃} : Finset V).card = 1 := by simp
    change ({x, y₁, y₂, y₃} : Finset V).card ≤ 4
    omega
  have hOutside : ∃ a, a ∉ used := by
    by_contra! h
    have hAll : used = Finset.univ := Finset.eq_univ_of_forall h
    rw [hAll, Finset.card_univ] at hc
    omega
  obtain ⟨a, ha⟩ := hOutside
  obtain ⟨hax, ha₁, ha₂, ha₃⟩ : a ≠ x ∧ a ≠ y₁ ∧ a ≠ y₂ ∧ a ≠ y₃ := by
    simpa [used] using ha
  exact ⟨triangularPair x a hax.symm,
    ⟨pair_ne_of_mem hax.symm h₁ ha₁, x, by simp, hx₁⟩,
    ⟨pair_ne_of_mem hax.symm h₂ ha₂, x, by simp, hx₂⟩,
    ⟨pair_ne_of_mem hax.symm h₃ ha₃, x, by simp, hx₃⟩⟩

/-- EPPA for the canonical inclusion of the selected edges of a triangular graph. -/
abbrev TriangularSelectionEPPA {V : Type*} (S : Set (TwoSet V)) : Prop :=
  IsEPPAEmbedding ((triangularGraph V).induce S) (triangularGraph V)
    ⟨Subtype.val, Subtype.val_injective⟩

private theorem eppa_moves_triples {V : Type*}
    {S : Set (TwoSet V)} (hEPPA : TriangularSelectionEPPA S)
    (u v : Fin 3 → S) (hu : Function.Injective u) (hv : Function.Injective v)
    (huAdj : ∀ i j, i ≠ j → ((triangularGraph V).induce S).Adj (u i) (u j))
    (hvAdj : ∀ i j, i ≠ j → ((triangularGraph V).induce S).Adj (v i) (v j)) :
    ∃ q, IsGraphAutomorphism (triangularGraph V) q ∧
      ∀ i, q (u i).val = (v i).val := by
  classical
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair u v hu hv
  let D := (Finset.univ : Finset (Fin 3)).image u
  have hPartial : IsPartialGraphAutomorphism ((triangularGraph V).induce S) D p := by
    intro a b ha hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    rw [hp, hp]
    by_cases hij : i = j
    · subst j
      simp
    · exact ⟨fun _ => hvAdj i j hij, fun _ => huAdj i j hij⟩
  obtain ⟨q, hq, hMap⟩ := hEPPA.2 D p hPartial
  refine ⟨q, hq, fun i => ?_⟩
  have hi : u i ∈ D := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hm := hMap (u i) hi
  change q (u i).val = (p (u i)).val at hm
  rwa [hp i] at hm

private theorem triple_injective {α : Type*} {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (fun i : Fin 3 => if i = 0 then a else if i = 1 then b else c) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem triple_adjacent {α : Type*} {G : SimpleGraph α} {a b c : α}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    ∀ i j : Fin 3, i ≠ j →
      G.Adj (if i = 0 then a else if i = 1 then b else c)
        (if j = 0 then a else if j = 1 then b else c) := by
  intro i j hij
  have hba := hab.symm
  have hca := hac.symm
  have hcb := hbc.symm
  fin_cases i <;> fin_cases j <;> simp_all

/-- An EPPA selection of at least five underlying points cannot contain both
the edges of a triangle and three distinct edges through a point. -/
theorem triangularGraph_no_root_triangle_and_star {V : Type*} [Fintype V] [DecidableEq V]
    {S : Set (TwoSet V)} (hV : 5 ≤ Fintype.card V) (hEPPA : TriangularSelectionEPPA S)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu₁ : triangularPair a b hab ∈ S) (hu₂ : triangularPair a c hac ∈ S) (hu₃ : triangularPair b c hbc ∈ S)
    (x : V) (v₁ v₂ v₃ : S) (hv₁₂ : v₁ ≠ v₂) (hv₁₃ : v₁ ≠ v₃) (hv₂₃ : v₂ ≠ v₃)
    (hx₁ : x ∈ v₁.val.val) (hx₂ : x ∈ v₂.val.val) (hx₃ : x ∈ v₃.val.val) : False := by
  let u₁ : S := ⟨triangularPair a b hab, hu₁⟩
  let u₂ : S := ⟨triangularPair a c hac, hu₂⟩
  let u₃ : S := ⟨triangularPair b c hbc, hu₃⟩
  let u : Fin 3 → S := fun i => if i = 0 then u₁ else if i = 1 then u₂ else u₃
  let v : Fin 3 → S := fun i => if i = 0 then v₁ else if i = 1 then v₂ else v₃
  obtain ⟨hau₁₂, hau₁₃, hau₂₃⟩ := root_pairs_adjacent hab hac hbc
  have huInj : Function.Injective u :=
    triple_injective (fun h => hau₁₂.1 (congrArg Subtype.val h))
      (fun h => hau₁₃.1 (congrArg Subtype.val h)) (fun h => hau₂₃.1 (congrArg Subtype.val h))
  have huAdj : ∀ i j, i ≠ j → ((triangularGraph V).induce S).Adj (u i) (u j) :=
    @triple_adjacent S ((triangularGraph V).induce S) u₁ u₂ u₃ hau₁₂ hau₁₃ hau₂₃
  have hvAdj : ∀ i j, i ≠ j → ((triangularGraph V).induce S).Adj (v i) (v j) :=
    @triple_adjacent S ((triangularGraph V).induce S) v₁ v₂ v₃
      ⟨fun h => hv₁₂ (Subtype.ext h), x, hx₁, hx₂⟩
      ⟨fun h => hv₁₃ (Subtype.ext h), x, hx₁, hx₃⟩
      ⟨fun h => hv₂₃ (Subtype.ext h), x, hx₂, hx₃⟩
  obtain ⟨q, hq, hMap⟩ := eppa_moves_triples hEPPA u v huInj
    (triple_injective hv₁₂ hv₁₃ hv₂₃) huAdj hvAdj
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := fourth_for_star hV x v₁.val v₂.val v₃.val hx₁ hx₂ hx₃
  have moved (i : Fin 3) (hi : (triangularGraph V).Adj w (v i).val) :
      (triangularGraph V).Adj (q.symm w) (u i).val := by
    apply (hq (q.symm w) (u i).val).mpr
    simpa only [q.apply_symm_apply, hMap i] using hi
  exact no_fourth_for_root_triangle hab hac hbc (q.symm w)
    (moved 0 (by simpa [v] using hw₁)) (moved 1 (by simpa [v] using hw₂))
    (moved 2 (by simpa [v] using hw₃))

/-- The selected edges incident with a point, counted in the fixed embedding. -/
private def incidentEdgeCount {V : Type*} [DecidableEq V] {S : Set (TwoSet V)}
    [Fintype S] (x : V) : ℕ :=
  ((Finset.univ : Finset S).filter (fun e => x ∈ e.val.val)).card

private theorem incidentEdgeCount_le_two {V : Type*} [Fintype V] [DecidableEq V]
    {S : Set (TwoSet V)} [Fintype S] (hV : 5 ≤ Fintype.card V)
    (hEPPA : TriangularSelectionEPPA S)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu₁ : triangularPair a b hab ∈ S) (hu₂ : triangularPair a c hac ∈ S)
    (hu₃ : triangularPair b c hbc ∈ S) (x : V) :
    incidentEdgeCount (S := S) x ≤ 2 := by
  by_contra! h
  obtain ⟨e₁, he₁, e₂, he₂, e₃, he₃, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.mp h
  exact triangularGraph_no_root_triangle_and_star hV hEPPA hab hac hbc hu₁ hu₂ hu₃
    x e₁ e₂ e₃ h₁₂ h₁₃ h₂₃
    (Finset.mem_filter.mp he₁).2 (Finset.mem_filter.mp he₂).2 (Finset.mem_filter.mp he₃).2

private theorem card_selected_le_points {V : Type*} [Fintype V] [DecidableEq V]
    {S : Set (TwoSet V)} [Fintype S] (h : ∀ x : V, incidentEdgeCount (S := S) x ≤ 2) :
    Fintype.card S ≤ Fintype.card V := by
  classical
  have hEdges : 2 * Fintype.card S = ∑ x : V, incidentEdgeCount (S := S) x := by
    symm
    calc
      ∑ x : V, incidentEdgeCount (S := S) x =
          ∑ x : V, ∑ e : S, if x ∈ e.val.val then 1 else 0 := by
        simp [incidentEdgeCount]
      _ = ∑ e : S, ∑ x : V, if x ∈ e.val.val then 1 else 0 := Finset.sum_comm
      _ = 2 * Fintype.card S := by
        simp [mul_comm, show ∀ e : S, e.val.val.card = 2 from fun e => e.val.property]
  have hBound : (∑ x : V, incidentEdgeCount (S := S) x) ≤ ∑ _ : V, (2 : ℕ) :=
    Finset.sum_le_sum (fun x _ => h x)
  simp [mul_comm (Fintype.card V) 2] at hBound
  omega

private theorem card_selection_five_le_four {V : Type*} [Fintype V] [DecidableEq V]
    {S : Set (TwoSet V)} [Fintype S] (hV : Fintype.card V = 5)
    (hEPPA : TriangularSelectionEPPA S)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hu₁ : triangularPair a b hab ∈ S) (hu₂ : triangularPair a c hac ∈ S)
    (hu₃ : triangularPair b c hbc ∈ S) : Fintype.card S ≤ 4 := by
  classical
  let u₁ : S := ⟨triangularPair a b hab, hu₁⟩
  let u₂ : S := ⟨triangularPair a c hac, hu₂⟩
  let u₃ : S := ⟨triangularPair b c hbc, hu₃⟩
  have hV' : 5 ≤ Fintype.card V := hV.ge
  have hTwo (x : V) (e₁ e₂ : S) (hne : e₁ ≠ e₂)
      (h₁ : x ∈ e₁.val.val) (h₂ : x ∈ e₂.val.val) (e : S)
      (he : x ∈ e.val.val) : e = e₁ ∨ e = e₂ := by
    by_contra! hh
    exact triangularGraph_no_root_triangle_and_star hV' hEPPA hab hac hbc
      hu₁ hu₂ hu₃ x e₁ e₂ e hne hh.1.symm hh.2.symm h₁ h₂ he
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := root_pairs_adjacent hab hac hbc
  let selected : Finset (Finset V) :=
    (Finset.univ : Finset S).map ⟨fun e => e.val.val,
      fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  let roots : Finset (Finset V) := {u₁.val.val, u₂.val.val, u₃.val.val}
  let outside : Finset V := (Finset.univ : Finset V) \ {a, b, c}
  have hOutside : outside.card = 2 := by
    change ((Finset.univ : Finset V) \ {a, b, c}).card = 2
    have hc : ({a, b, c} : Finset V).card = 3 :=
      Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hV, hc]
  have hSub : selected ⊆ roots ∪ outside.powersetCard 2 := by
    intro X hX
    obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hX
    change e.val.val ∈ roots ∪ outside.powersetCard 2
    rw [Finset.mem_union]
    by_cases ha : a ∈ e.val.val
    · left
      rcases hTwo a u₁ u₂ (fun h => h₁₂.1 (congrArg Subtype.val h))
          (by simp [u₁]) (by simp [u₂]) e ha with rfl | rfl <;> simp [roots]
    by_cases hb : b ∈ e.val.val
    · left
      rcases hTwo b u₁ u₃ (fun h => h₁₃.1 (congrArg Subtype.val h))
          (by simp [u₁]) (by simp [u₃]) e hb with rfl | rfl <;> simp [roots]
    by_cases hc : c ∈ e.val.val
    · left
      rcases hTwo c u₂ u₃ (fun h => h₂₃.1 (congrArg Subtype.val h))
          (by simp [u₂]) (by simp [u₃]) e hc with rfl | rfl <;> simp [roots]
    right
    refine Finset.mem_powersetCard.mpr ⟨fun x hx => ?_, e.val.property⟩
    have hxa : x ≠ a := fun eq => ha (eq ▸ hx)
    have hxb : x ≠ b := fun eq => hb (eq ▸ hx)
    have hxc : x ≠ c := fun eq => hc (eq ▸ hx)
    simp [outside, hxa, hxb, hxc]
  have hcRoots : roots.card ≤ 3 := by
    have h₁' := Finset.card_insert_le u₁.val.val ({u₂.val.val, u₃.val.val} : Finset (Finset V))
    have h₂' := Finset.card_insert_le u₂.val.val ({u₃.val.val} : Finset (Finset V))
    have h₃' : ({u₃.val.val} : Finset (Finset V)).card = 1 := by simp
    change ({u₁.val.val, u₂.val.val, u₃.val.val} : Finset (Finset V)).card ≤ 3
    omega
  have hcSelected : selected.card = Fintype.card S := by simp [selected]
  have hcFree : (outside.powersetCard 2).card = 1 := by
    rw [Finset.card_powersetCard, hOutside]
    decide
  have hCount := (Finset.card_le_card hSub).trans (Finset.card_union_le roots (outside.powersetCard 2))
  omega

/-- The cardinality of the triangular host on a finite type of points. -/
theorem triangularGraph_card {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype.card (TwoSet V) = (Fintype.card V).choose 2 := by
  calc
    Fintype.card (TwoSet V) = ((Finset.univ : Finset V).powersetCard 2).card :=
      Fintype.card_of_subtype (p := fun s : Finset V => s.card = 2) _
        (fun s => by simp [Finset.mem_powersetCard])
    _ = (Fintype.card V).choose 2 := by rw [Finset.card_powersetCard, Finset.card_univ]

/-- For a selection of at least half the vertices of a triangular host,
EPPA is equivalent to triangle-freeness of the selected edges on the given
underlying points. -/
theorem triangularGraph_eppa_iff_triangleFreeEdges {V : Type*} [Fintype V] [DecidableEq V]
    (S : Set (TwoSet V)) [Fintype S] (hV : 5 ≤ Fintype.card V)
    (hLarge : Fintype.card (TwoSet V) ≤ 2 * Fintype.card S) :
    TriangularSelectionEPPA S ↔ TriangleFreeEdges S := by
  constructor
  · intro hEPPA a b c hab hac hbc hu₁ hu₂ hu₃
    rw [triangularGraph_card] at hLarge
    by_cases h5 : Fintype.card V = 5
    · have hBound := card_selection_five_le_four h5 hEPPA hab hac hbc hu₁ hu₂ hu₃
      rw [h5] at hLarge
      have hChoose : Nat.choose 5 2 = 10 := by decide
      omega
    · have hBound := card_selected_le_points
        (incidentEdgeCount_le_two hV hEPPA hab hac hbc hu₁ hu₂ hu₃)
      have hMul := Nat.mul_le_mul_left (Fintype.card V)
        (show 5 ≤ Fintype.card V - 1 by omega)
      rw [Nat.choose_two_right] at hLarge
      omega
  · exact triangularGraph_eppa_induce S

end EPPAIII.Primitive
