import EPPAIII.EPPA.BaseRelabel
import EPPAIII.Primitive.TriangularObstruction

/-!
# Triangular EPPA witnesses for an arbitrary induced embedding
-/

namespace EPPAIII.Primitive

/-- The triangular half-order classification, stated in the fixed-embedding
interface used by the primitive classification. -/
theorem triangularGraph_eppa_iff_triangleFreeRange {U V : Type*}
    [Fintype U] [Fintype V] [DecidableEq V]
    (G : SimpleGraph U) (e : U ↪ TwoSet V)
    (hInduced : IsInducedGraphEmbedding G (triangularGraph V) e)
    (hV : 5 ≤ Fintype.card V)
    (hLarge : Fintype.card (TwoSet V) ≤ 2 * Fintype.card U) :
    IsEPPAEmbedding G (triangularGraph V) e ↔ TriangleFreeEdges (Set.range e) := by
  classical
  let f := Equiv.ofInjective e e.injective
  let : Fintype (Set.range e) := Fintype.ofEquiv U f
  let incl : Set.range e ↪ TwoSet V := Function.Embedding.subtype _
  have hMap (x : Set.range e) : e (f.symm x) = x :=
    congrArg Subtype.val (f.apply_symm_apply x)
  have hCard : Fintype.card (Set.range e) = Fintype.card U := Fintype.card_congr f.symm
  have hLarge' : Fintype.card (TwoSet V) ≤ 2 * Fintype.card (Set.range e) := by
    simpa only [hCard] using hLarge
  have hIff := triangularGraph_eppa_iff_triangleFreeEdges (Set.range e) hV hLarge'
  constructor
  · intro heppa
    apply hIff.mp
    have hRelabel := eppa_relabel_base G (triangularGraph V) e heppa f.symm
      ((triangularGraph V).induce (Set.range e)) (by
        intro x y
        change (triangularGraph V).Adj (↑x) (↑y) ↔ G.Adj (f.symm x) (f.symm y)
        rw [hInduced (f.symm x) (f.symm y), hMap, hMap])
    have hEq : relabelEmbedding e f.symm = incl := by
      apply Function.Embedding.ext
      exact hMap
    rwa [hEq] at hRelabel
  · intro hTriangleFree
    have heppa := hIff.mpr hTriangleFree
    have hRelabel := eppa_relabel_base ((triangularGraph V).induce (Set.range e))
      (triangularGraph V) incl heppa f G (by
        intro x y
        exact hInduced x y)
    have hEq : relabelEmbedding incl f = e := by
      apply Function.Embedding.ext
      intro x
      rfl
    exact hEq ▸ hRelabel

end EPPAIII.Primitive
