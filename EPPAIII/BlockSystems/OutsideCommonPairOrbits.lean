import EPPAIII.BlockSystems.UnequalCase1Matching
import EPPAIII.BlockSystems.TransitivePartition

/-!
# Exceptional C5 case: no invariant distinguished base pair

The missing C5 step in Lemma 3.18 excludes a bipartite cross-edge
graph with a four-cycle and six-cycle. The four-cycle would single
out exactly one pair of base vertices having two common neighbours
in the complementary half.

We prove the general structural obstruction here: under genuine EPPA,
full base automorphisms preserve the count of common neighbours in
the outside half. In a vertex-transitive base of more than two
vertices no property may distinguish a unique unordered base pair.
The separate finite graph observation that C4 ⊔ C6 has precisely
one such pair is not assumed to be proved by this file.

This module is reusable for the R3 orbit analysis as well.
-/

namespace EPPAIII.BlockSystems

/-- Outside common neighbours of two selected base vertices in
an arbitrary finite induced EPPA host. -/
noncomputable def outsideCommonNeighbourFinset {V W : Type*}
    [Fintype W] (H : SimpleGraph W) (e : V ↪ W)
    (x y : V) : Finset W := by
  classical
  exact (Finset.univ : Finset W).filter (fun w =>
    w ∉ Set.range e ∧ H.Adj (e x) w ∧ H.Adj (e y) w)

/-- An actual full automorphism of the base extends by EPPA and
preserves the count of common neighbours in the complementary half.
No coherent choice of extensions is assumed. -/
theorem outside_common_neighbour_card_base_automorphism
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (p : Equiv.Perm V) (hp : IsGraphAutomorphism G p)
    (x y : V) :
    (outsideCommonNeighbourFinset H e x y).card =
      (outsideCommonNeighbourFinset H e (p x) (p y)).card := by
  classical
  have hPartial : IsPartialGraphAutomorphism G Finset.univ p :=
    graphAuto_restricts G p hp Finset.univ
  obtain ⟨q,hq,hExtend⟩ :=
    heppa.2 Finset.univ p hPartial
  have hImage (v : V) : q (e v) = e (p v) :=
    hExtend v (Finset.mem_univ _)
  have hSelected (w : W) :
      w ∈ Set.range e ↔ q w ∈ Set.range e := by
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨p v,(hImage v).symm⟩
    · rintro ⟨v,hv⟩
      refine ⟨p.symm v,?_⟩
      apply q.injective
      calc
        q (e (p.symm v)) = e (p (p.symm v)) := hImage _
        _ = e v := by simp
        _ = q w := hv
  have hIff (w : W) :
      w ∈ outsideCommonNeighbourFinset H e x y ↔
        q w ∈ outsideCommonNeighbourFinset H e (p x) (p y) := by
    simp only [outsideCommonNeighbourFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw,hx,hy⟩
      refine ⟨(not_congr (hSelected w)).mp hw,?_,?_⟩
      · simpa only [hImage x] using (hq (e x) w).mp hx
      · simpa only [hImage y] using (hq (e y) w).mp hy
    · rintro ⟨hw,hx,hy⟩
      refine ⟨(not_congr (hSelected w)).mpr hw,?_,?_⟩
      · apply (hq (e x) w).mpr
        simpa only [hImage x] using hx
      · apply (hq (e y) w).mpr
        simpa only [hImage y] using hy
  refine Finset.card_bij'
    (fun w _ => q w) (fun w _ => q.symm w) ?_ ?_ ?_ ?_
  · intro w hw
    exact (hIff w).mp hw
  · intro w hw
    apply (hIff (q.symm w)).mpr
    simpa using hw
  · intro w hw
    simp
  · intro w hw
    simp

/-- Every nonempty subset invariant under all automorphisms of
a vertex-transitive graph is the full vertex set. -/
theorem invariant_nonempty_finset_of_vertex_transitive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms G)
    (S : Finset V) (hNonempty : S.Nonempty)
    (hInvariant : ∀ p : Equiv.Perm V, IsGraphAutomorphism G p →
      S.image p = S) :
    S = Finset.univ := by
  classical
  obtain ⟨x,hx⟩ := hNonempty
  ext y
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨p,hp,hpx⟩ := hTrans x y
  have hMem : p x ∈ S := by
    rw [← hInvariant p hp]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  simpa only [hpx] using hMem

/-- A transitive base with more than two vertices cannot have a
unique unordered pair with two outside common neighbours in an
EPPA witness. This is exactly the C4+ C6 exclusion's orbit step. -/
theorem no_unique_outside_double_common_pair_of_transitive_eppa
    {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms G)
    (hLarge : 2 < Fintype.card V)
    (a b : V) (hab : a ≠ b)
    (hPair :
      (outsideCommonNeighbourFinset H e a b).card = 2)
    (hUnique : ∀ x y : V, x ≠ y →
      (outsideCommonNeighbourFinset H e x y).card = 2 →
      ({x,y} : Finset V) = {a,b}) : False := by
  classical
  let S : Finset V := {a,b}
  have hInvariant : ∀ p : Equiv.Perm V,
      IsGraphAutomorphism G p → S.image p = S := by
    intro p hp
    have hCount :
        (outsideCommonNeighbourFinset H e (p a) (p b)).card = 2 := by
      calc
        (outsideCommonNeighbourFinset H e (p a) (p b)).card =
            (outsideCommonNeighbourFinset H e a b).card :=
          (outside_common_neighbour_card_base_automorphism
            G H e heppa p hp a b).symm
        _ = 2 := hPair
    have hEqual := hUnique (p a) (p b) (p.injective.ne hab) hCount
    simpa [S] using hEqual
  have hSCard : S.card = 2 := by
    simp [S, hab]
  have hSNonempty : S.Nonempty :=
    Finset.card_pos.mp (by omega)
  have hAll :=
    invariant_nonempty_finset_of_vertex_transitive
      G hTrans S hSNonempty hInvariant
  have hCard : Fintype.card V = 2 := by
    calc
      Fintype.card V = (Finset.univ : Finset V).card := by simp
      _ = S.card := congrArg Finset.card hAll.symm
      _ = 2 := hSCard
  omega

end EPPAIII.BlockSystems
