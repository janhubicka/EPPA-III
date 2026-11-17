import EPPAIII.Primitive.SRGIndependentBound
import EPPAIII.CliqueCovers.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum

/-! # Structural refinements of the exceptional affine parameter tests -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- With complete off-diagonal cross blocks before complementation, two
different blocks on opposite sides supply an independent set of size `t+t`. -/
theorem complement_cover_independent_two_blocks {s t : ℕ} (hs : 2 ≤ s)
    (X : CrossType) :
    ∃ f : Fin (t + t) ↪ CoverVertex s t,
      ∀ a b, ¬ (coverGraph s t X true)ᶜ.Adj (f a) (f b) := by
  let i : Fin s := ⟨0, by omega⟩
  let j : Fin s := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  let g : Fin t ⊕ Fin t ↪ CoverVertex s t :=
    ⟨Sum.elim (left i) (right j), by
      intro a b h
      cases a <;> cases b
      · have hEq := congrArg (fun v : CoverVertex s t => v.2.2) h
        exact congrArg Sum.inl hEq
      · have hSide := congrArg (fun v : CoverVertex s t => v.1) h
        exact Bool.noConfusion hSide
      · have hSide := congrArg (fun v : CoverVertex s t => v.1) h
        exact Bool.noConfusion hSide
      · have hEq := congrArg (fun v : CoverVertex s t => v.2.2) h
        exact congrArg Sum.inr hEq⟩
  have hg : ∀ a b, ¬ (coverGraph s t X true)ᶜ.Adj (g a) (g b) := by
    rintro (u | u) (v | v) h
    · change (coverGraph s t X true)ᶜ.Adj (left i u) (left i v) at h
      exact h.2 ((left_induced X true i i u v).mpr
        ⟨rfl, fun he => h.1 (congrArg (left i) he)⟩)
    · change (coverGraph s t X true)ᶜ.Adj (left i u) (right j v) at h
      exact h.2 ((cross_off_iff X true i j u v hij).mpr rfl)
    · change (coverGraph s t X true)ᶜ.Adj (right j u) (left i v) at h
      exact h.2 ((cross_off_iff X true i j v u hij).mpr rfl).symm
    · change (coverGraph s t X true)ᶜ.Adj (right j u) (right j v) at h
      exact h.2 ((right_induced X true j j u v).mpr
        ⟨rfl, fun he => h.1 (congrArg (right j) he)⟩)
  let θ : Fin (t + t) ≃ Fin t ⊕ Fin t := finSumFinEquiv.symm
  exact ⟨θ.toEmbedding.trans g, fun a b => hg (θ a) (θ b)⟩

/-- A same-block nonedge in a complementary cover has at least
`(s-1)*t` neighbours in common, coming from all other same-side blocks.
An external root adjacent to every vertex of the embedded cover
contributes one further common neighbour. -/
theorem complement_cover_common_neighbors_with_root
    {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {s t : ℕ} (hs : 0 < s) (ht : 2 ≤ t) (X : CrossType) (Y : Bool)
    (e : (coverGraph s t X Y)ᶜ ↪g H) (root : V)
    (hroot : ∀ x, H.Adj root (e x)) :
    ∃ x y : V, x ≠ y ∧ ¬ H.Adj x y ∧
      (s - 1) * t + 1 ≤ Fintype.card (H.commonNeighbors x y) := by
  classical
  let i : Fin s := ⟨0, hs⟩
  let a : Fin t := ⟨0, by omega⟩
  let b : Fin t := ⟨1, by omega⟩
  have hab : a ≠ b := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  have hadj : (coverGraph s t X Y).Adj (left i a) (left i b) :=
    (left_induced X Y i i a b).mpr ⟨rfl, hab⟩
  refine ⟨e (left i a), e (left i b), e.injective.ne hadj.ne,
    fun h => (e.map_rel_iff.mp h).2 hadj, ?_⟩
  let I := (Finset.univ : Finset (Fin s)).erase i
  have hCard : Fintype.card I = s - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  have hCross (z : Fin t) (j : I) (c : Fin t) :
      (coverGraph s t X Y)ᶜ.Adj (left i z) (left j.val c) := by
    have hj : i ≠ j.val := (Finset.mem_erase.mp j.property).1.symm
    exact ⟨fun h => hj (congrArg (fun v : CoverVertex s t => v.2.1) h),
      fun h => hj ((left_induced X Y i j.val z c).mp h).1⟩
  let f : Unit ⊕ (I × Fin t) → H.commonNeighbors (e (left i a)) (e (left i b)) :=
    Sum.elim (fun _ => ⟨root, (hroot _).symm, (hroot _).symm⟩)
      (fun x => ⟨e (left x.1.val x.2), e.map_rel_iff.mpr (hCross a x.1 x.2),
        e.map_rel_iff.mpr (hCross b x.1 x.2)⟩)
  have hinj : Function.Injective f := by
    intro x y he
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · have heq : root = e (left y.1.val y.2) := congrArg Subtype.val he
      exact ((hroot (left y.1.val y.2)).ne heq).elim
    · have heq : e (left x.1.val x.2) = root := congrArg Subtype.val he
      exact ((hroot (left x.1.val x.2)).ne heq.symm).elim
    · have hval : left x.1.val x.2 = left y.1.val y.2 :=
        e.injective (congrArg Subtype.val he)
      exact congrArg Sum.inr (Prod.ext
        (Subtype.ext (congrArg (fun v : CoverVertex s t => v.2.1) hval))
        (congrArg (fun v : CoverVertex s t => v.2.2) hval))
  have hb := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod,
    Fintype.card_fin, hCard, Nat.add_comm] using hb

theorem affine_2401_240_no_sixty_clique {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 2401 240 59 20)
    (f : Fin 60 ↪ V) (hf : ∀ i j, i ≠ j → H.Adj (f i) (f j)) : False := by
  have hc : ∀ i j, ¬ Hᶜ.Adj (f i) (f j) := by
    intro i j hij
    exact hij.2 (hf i j (fun e => hij.1 (congrArg f e)))
  have hcomp : Hᶜ.IsSRGWith 2401 2160 1939 1980 := h.compl
  have hn := srg_independent_size_bound_outside Hᶜ hcomp f hc
  norm_num at hn

theorem affine_2401_480_no_hundred_twenty_clique {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 2401 480 119 90)
    (f : Fin 120 ↪ V) (hf : ∀ i j, i ≠ j → H.Adj (f i) (f j)) : False := by
  have hc : ∀ i j, ¬ Hᶜ.Adj (f i) (f j) := by
    intro i j hij
    exact hij.2 (hf i j (fun e => hij.1 (congrArg f e)))
  have hcomp : Hᶜ.IsSRGWith 2401 1920 1529 1560 := h.compl
  have hn := srg_independent_size_bound_outside Hᶜ hcomp f hc
  norm_num at hn

/-- The only numerical survivor at order 15625 requires this complemented
cover as an induced subgraph of the host. -/
theorem affine_15625_no_complemented_cover {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (h : H.IsSRGWith 15625 7560 3655 3660)
    (X : CrossType) (e : (coverGraph 30 126 X true)ᶜ ↪g H) : False := by
  obtain ⟨f, hf⟩ := complement_cover_independent_two_blocks (t := 126) (s := 30) (by decide) X
  have hc : ∀ i j, ¬ H.Adj (e (f i)) (e (f j)) :=
    fun i j hij => hf i j (e.map_rel_iff.mp hij)
  have hn := srg_independent_size_bound_outside H h (f.trans e.toEmbedding) hc
  norm_num at hn

end EPPAIII.Primitive
