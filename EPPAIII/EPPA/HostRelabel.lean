import EPPAIII.EPPA.Definitions
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Relabelling the host graph of an EPPA embedding
-/

namespace EPPAIII

/-- Transport an EPPA embedding along an isomorphism of witness graphs. -/
theorem eppa_relabel_host {V W X : Type*} (G : SimpleGraph V)
    {H : SimpleGraph W} {K : SimpleGraph X} (e : V ↪ W)
    (h : IsEPPAEmbedding G H e) (φ : H ≃g K) :
    IsEPPAEmbedding G K (e.trans φ.toEquiv.toEmbedding) := by
  let f := φ.toEquiv
  have hMap (x y : W) : H.Adj x y ↔ K.Adj (f x) (f y) := φ.map_rel_iff.symm
  constructor
  · intro x y
    exact (h.1 x y).trans (hMap (e x) (e y))
  · intro D p hp
    obtain ⟨q, hq, hExt⟩ := h.2 D p hp
    refine ⟨(f.symm.trans q).trans f, ?_, ?_⟩
    · intro x y
      change K.Adj x y ↔ K.Adj (f (q (f.symm x))) (f (q (f.symm y)))
      simpa only [Equiv.apply_symm_apply] using ((hMap (f.symm x) (f.symm y)).symm.trans
        ((hq (f.symm x) (f.symm y)).trans (hMap (q (f.symm x)) (q (f.symm y)))))
    · intro x hx
      change f (q (f.symm (f (e x)))) = f (e (p x))
      rw [f.symm_apply_apply, hExt x hx]

end EPPAIII
