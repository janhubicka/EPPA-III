import EPPAIII.BlockSystems.RankThreeImprimitiveHomogeneity
import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# Pair-orbit assembly for the small-witness rank-three reduction

The small-witness proposition separates into two parts:
* geometric/group-theoretic pair coverage: every ordered pair of distinct
  host vertices can be moved inside the distinguished induced copy;
* EPPA orbit assembly: once a pair is inside the copy, any other pair of
  the same adjacency status can be reached by an EPPA extension.

This file proves the second part with the actual fixed-embedding EPPA
interface. It does not assert pair coverage or primitivity; those are
separate obligations of the small-witness rank-three reduction.
-/

namespace EPPAIII.BlockSystems

/-- Every ordered host pair can be moved, by a graph automorphism, into
an ordered pair in the designated embedded copy. -/
def HasSelectedPairCoverage {V W : Type*}
    (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  ∀ u v : W, u ≠ v →
    ∃ (x y : V) (q : Equiv.Perm W),
      x ≠ y ∧ IsGraphAutomorphism H q ∧
      q u = e x ∧ q v = e y

/-- EPPA sends any ordered pair in the distinguished copy to any
other such ordered pair with the same adjacency status. -/
theorem eppa_embedded_two_point_orbit {V W : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (x y a b : V) (hxy : x ≠ y) (hab : a ≠ b)
    (hStatus : H.Adj (e x) (e y) ↔ H.Adj (e a) (e b)) :
    ∃ q : Equiv.Perm W,
      IsGraphAutomorphism H q ∧ q (e x) = e a ∧ q (e y) = e b := by
  classical
  have hBase : G.Adj x y ↔ G.Adj a b :=
    (heppa.1 x y).trans (hStatus.trans (heppa.1 a b).symm)
  obtain ⟨p,hpx,hpy,hPartial⟩ :=
    EPPAIII.DoubleCover.partial_of_two_maps G x y a b hxy hab hBase
  obtain ⟨q,hq,hExtend⟩ :=
    heppa.2 ({x,y} : Finset V) p hPartial
  refine ⟨q,hq,?_,?_⟩
  · simpa [hpx] using (hExtend x (by simp))
  · simpa [hpy] using (hExtend y (by simp))

/-- Pair coverage and EPPA imply the exact source-facing
rank-three ordered-pair orbit conclusion, without assuming the
host graph is either nonempty or noncomplete. -/
theorem eppa_pair_status_orbits_of_selected_coverage {V W : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hCoverage : HasSelectedPairCoverage H e) :
    HasOrderedPairOrbitByStatus H := by
  classical
  intro u v u' v' huv huv' hStatus
  obtain ⟨x,y,q,hxy,hq,hqu,hqv⟩ := hCoverage u v huv
  obtain ⟨a,b,r,hab,hr,hru,hrv⟩ := hCoverage u' v' huv'
  have hEmbeddedStatus : H.Adj (e x) (e y) ↔ H.Adj (e a) (e b) := by
    calc
      H.Adj (e x) (e y) ↔ H.Adj u v := by
        simpa [hqu,hqv] using (hq u v).symm
      _ ↔ H.Adj u' v' := hStatus
      _ ↔ H.Adj (e a) (e b) := by
        simpa [hru,hrv] using (hr u' v')
  obtain ⟨p,hp,hpx,hpy⟩ :=
    eppa_embedded_two_point_orbit G H e heppa
      x y a b hxy hab hEmbeddedStatus
  have hInv : IsGraphAutomorphism H r.symm := by
    intro z t
    simpa using (hr (r.symm z) (r.symm t)).symm
  let f : Equiv.Perm W := (q.trans p).trans r.symm
  have hAut : IsGraphAutomorphism H f := by
    intro z t
    exact (hq z t).trans ((hp (q z) (q t)).trans
      (hInv (p (q z)) (p (q t))))
  refine ⟨f,hAut,?_,?_⟩
  · change r.symm (p (q u)) = u'
    rw [hqu,hpx,←hru]
    simp
  · change r.symm (p (q v)) = v'
    rw [hqv,hpy,←hrv]
    simp

/-- A vertex-transitive graph on two equally sized labelled sides,
with no edges on the first side, has no edges on the second side.
This is the half-edge-count step in the equality case of the
small-witness rank-three argument; it does NOT yet prove that an
invariant orbital graph contradicts primitivity. -/
theorem transitive_balanced_independent_half {V : Type*}
    [Fintype V] [Nonempty V]
    (F : SimpleGraph (Bool × V)) [DecidableRel F.Adj]
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms F)
    (hFirst : ∀ x y : V, ¬ F.Adj (false,x) (false,y)) :
    ∀ x y : V, ¬ F.Adj (true,x) (true,y) := by
  classical
  have hFirstBot : EPPAIII.CliqueCovers.sideGraph F false = ⊥ := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change F.Adj (false,x) (false,y) ↔ False
    exact ⟨hFirst x y, False.elim⟩
  have hSides :=
    EPPAIII.CliqueCovers.sideEdges_equal_of_transitive_graph F hTrans
  have hFirstZero : EPPAIII.CliqueCovers.sideEdgeCount F false = 0 := by
    simp [EPPAIII.CliqueCovers.sideEdgeCount,hFirstBot]
  have hSecondZero : EPPAIII.CliqueCovers.sideEdgeCount F true = 0 := by
    rw [←hSides]
    exact hFirstZero
  have hEmpty : (EPPAIII.CliqueCovers.sideGraph F true).edgeFinset = ∅ :=
    Finset.card_eq_zero.mp
      (by simpa [EPPAIII.CliqueCovers.sideEdgeCount] using hSecondZero)
  have hSecondBot : EPPAIII.CliqueCovers.sideGraph F true = ⊥ :=
    (SimpleGraph.edgeFinset_eq_empty).mp hEmpty
  intro x y h
  have hh : (EPPAIII.CliqueCovers.sideGraph F true).Adj x y := h
  rw [hSecondBot] at hh
  exact hh

end EPPAIII.BlockSystems
