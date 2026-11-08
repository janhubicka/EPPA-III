import EPPAIII.EPPA.InducedSubsetEPPA
import EPPAIII.BlockSystems.Basic
import EPPAIII.TwoGraphs.AllTransversalEppa

/-!
# The minimal three-point obstruction in an invariant-fibre Taylor double

If the natural fibres are preserved by every automorphism, selecting both
points of one fibre and a point of a second fibre prevents EPPA for that
specific selected induced subgraph. The proof uses genuine EPPA on the
selected subset and a two-point partial automorphism; no coherent lift
or assumption that a transversal is already an EPPA witness is needed.

This proves only the necessary side of the corrected manuscript
obstacle criterion. The positive direction requires every transversal
to have EPPA and the hereditary-EPPA theorem.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover
open EPPAIII.BlockSystems

/-- Invariance of Taylor fibres, expressed as an invariant block map. -/
theorem taylor_invariant_fibre_map
    {V : Type*}
    (G : SimpleGraph V)
    (hPairs : HasInvariantPairs (taylorPairGraph G)) :
    InvariantBlockMap (taylorPairGraph G)
      (fun w : Bool × V => w.2) := by
  intro q hq u v
  obtain ⟨σ,hσ⟩ := hPairs q hq
  change u.2 = v.2 ↔ (q u).2 = (q v).2
  rw [hσ u.1 u.2, hσ v.1 v.2]
  exact ⟨fun h => congrArg σ h, fun h => σ.injective h⟩

/-- From a third fibre, precisely one of the two points over x
has the same (nonedge) status as the mate pair over x. -/
theorem taylor_one_cross_nonedge
    {V : Type*}
    (G : SimpleGraph V) (x y : V) (b : Bool) :
    ¬ (taylorPairGraph G).Adj (false,x) (b,y) ∨
      ¬ (taylorPairGraph G).Adj (true,x) (b,y) := by
  change ¬ (x ≠ y ∧ (G.Adj x y ↔ (false : Bool) = b)) ∨
    ¬ (x ≠ y ∧ (G.Adj x y ↔ (true : Bool) = b))
  cases b <;> tauto

/-- A selected full fibre together with a third point from another
fibre is a genuine three-point EPPA obstruction when host automorphisms
preserve the natural fibres. -/
theorem taylor_full_fibre_with_third_not_eppa
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (S : Finset (Bool × V))
    (x y : V) (b : Bool) (hxy : x ≠ y)
    (hFalse : (false,x) ∈ S)
    (hTrue : (true,x) ∈ S)
    (hThird : (b,y) ∈ S) :
    ¬ IsEPPAOnSubset (taylorPairGraph G) S := by
  classical
  let H := taylorPairGraph G
  let F := selectedSubsetGraph H S
  let e := selectedSubsetInclusion S
  let block : Bool × V → V := fun w => w.2
  let u : {w : Bool × V // w ∈ S} := ⟨(false,x),hFalse⟩
  let v : {w : Bool × V // w ∈ S} := ⟨(true,x),hTrue⟩
  let z : {w : Bool × V // w ∈ S} := ⟨(b,y),hThird⟩
  have huv : u ≠ v := by
    intro h
    have heq : (false : Bool) = true :=
      congrArg (fun w : {w : Bool × V // w ∈ S} => w.1.1) h
    exact Bool.false_ne_true heq
  have huz : u ≠ z := by
    intro h
    have heq : x = y :=
      congrArg (fun w : {w : Bool × V // w ∈ S} => w.1.2) h
    exact hxy heq
  have hvz : v ≠ z := by
    intro h
    have heq : x = y :=
      congrArg (fun w : {w : Bool × V // w ∈ S} => w.1.2) h
    exact hxy heq
  have hMate : ¬ F.Adj u v := by
    change ¬ (H.Adj (false,x) (true,x))
    change ¬ (x ≠ x ∧ (G.Adj x x ↔ (false : Bool) = true))
    simp
  have hCross := taylor_one_cross_nonedge G x y b
  have hBlocks : InvariantBlockMap H block :=
    taylor_invariant_fibre_map G hPairs
  intro hEPPA
  have hHost : IsEPPAEmbedding F H e := hEPPA
  rcases hCross with hNoFalse | hNoTrue
  · have hNo : ¬ F.Adj u z := hNoFalse
    have hStatus : F.Adj u v ↔ F.Adj u z :=
      ⟨fun h => (hMate h).elim, fun h => (hNo h).elim⟩
    have hRel :=
      eppa_block_relation_two_point F H e hHost
        block hBlocks u v u z huv huz hStatus
    have hRel' : (x = x ↔ x = y) := hRel
    exact hxy (hRel'.mp rfl)
  · have hNo : ¬ F.Adj v z := hNoTrue
    have hStatus : F.Adj u v ↔ F.Adj v z :=
      ⟨fun h => (hMate h).elim, fun h => (hNo h).elim⟩
    have hRel :=
      eppa_block_relation_two_point F H e hHost
        block hBlocks u v v z huv hvz hStatus
    have hRel' : (x = x ↔ x = y) := hRel
    exact hxy (hRel'.mp rfl)

/-- Exact negative statement in the corrected obstacle item. -/
theorem taylor_ep_subset_has_no_full_fibre_and_third
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hPairs : HasInvariantPairs (taylorPairGraph G))
    (S : Finset (Bool × V))
    (hEPPA : IsEPPAOnSubset (taylorPairGraph G) S) :
    ¬ ∃ x y : V, ∃ b : Bool,
      x ≠ y ∧ (false,x) ∈ S ∧ (true,x) ∈ S ∧ (b,y) ∈ S := by
  rintro ⟨x,y,b,hxy,hFalse,hTrue,hThird⟩
  exact taylor_full_fibre_with_third_not_eppa
    G hPairs S x y b hxy hFalse hTrue hThird hEPPA

end EPPAIII.TwoGraphs
