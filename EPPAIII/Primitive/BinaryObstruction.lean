import EPPAIII.Primitive.TupleParityObstruction
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Logic.Equiv.Fintype

/-!
# A graph-invariant obstruction for the binary finite certificates

A graph isomorphism between two selected pieces extends to a partial
automorphism of the selected base. If one piece has even parity of
distinct nonneighbours at every host vertex and the other has odd parity
at some host vertex, no host automorphism can extend it.
-/

namespace EPPAIII.Primitive

/-- An induced isomorphism between selected pieces preserves any host
parity invariant if the whole selection has the EPPA property. -/
theorem not_eppa_of_tupleParity_zero_obstruction {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableEq W] [DecidableRel H.Adj]
    (e : V ↪ W) (A B : Finset V)
    (φ : G.induce (A : Set V) ≃g G.induce (B : Set V))
    (hEven : ∀ w, tupleParity H (fun a : A => e a) w = 0)
    (hOdd : ∃ w, tupleParity H (fun b : B => e b) w ≠ 0) :
    ¬ IsEPPAEmbedding G H e := by
  classical
  intro heppa
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun a : A => (a : V)) (fun a : A => ((φ a : B) : V))
    Subtype.val_injective (Subtype.val_injective.comp φ.injective)
  have hPartial : IsPartialGraphAutomorphism G A p := by
    intro x y hx hy
    rw [hp ⟨x, hx⟩, hp ⟨y, hy⟩]
    exact (φ.map_rel_iff (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).symm
  obtain ⟨q, hq, hExt⟩ := heppa.2 A p hPartial
  have hMap : q ∘ (fun a : A => e a) = (fun a : A => e (φ a)) := by
    funext a
    exact (hExt a a.property).trans (congrArg e (hp a))
  obtain ⟨w, hw⟩ := hOdd
  obtain ⟨x, rfl⟩ := q.surjective w
  apply hw
  have hParity := tupleParity_map H (fun a : A => e a) x q hq
  rw [hMap, hEven x] at hParity
  convert hParity using 1
  unfold tupleParity
  congr 1
  exact (Fintype.sum_equiv φ.toEquiv _ _ (fun _ => rfl)).symm

end EPPAIII.Primitive
