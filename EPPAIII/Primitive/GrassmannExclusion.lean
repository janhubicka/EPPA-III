import EPPAIII.Primitive.GrassmannRookEmbedding
import EPPAIII.Primitive.GrassmannRookObstruction
import EPPAIII.Primitive.GrassmannPentagonEmbedding
import EPPAIII.Primitive.CycleFiveCoverObstruction
import EPPAIII.Primitive.OrthogonalEightConstituents

/-! # Excluding the Grassmann family from the constituent-shape requirement -/

namespace EPPAIII.Primitive

open Module

/-- In dimension at least five, each rooted Grassmann constituent
violates the shape requirement for the primitive classification. -/
theorem grassmannGraph_constituents_exclude_forms
    {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (root : GrassmannPlane F V) (hDim : 5 ≤ finrank F V) :
    ¬ HasCliqueUnionOrCoverModel (localGraph (grassmannGraph F V) root) ∧
      ¬ HasCliqueUnionOrCoverModel (nonlocalGraph (grassmannGraph F V) root) := by
  let grid := grassmannGraph_local_rookThree root (by omega)
  let cycle := grassmannGraph_nonlocal_fiveCycle root hDim
  constructor
  · rintro (⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩)
    · rcases h with h | h
      · obtain ⟨iso⟩ := h
        exact (no_clique_union_or_compl_of_induced_rookThree grid s t).1.false iso
      · obtain ⟨iso⟩ := h
        exact (no_clique_union_or_compl_of_induced_rookThree grid s t).2.false iso
    · rcases h with h | h
      · obtain ⟨iso⟩ := h
        exact (no_cover_or_compl_of_induced_rookThree grid s t X Y).1.false iso
      · obtain ⟨iso⟩ := h
        exact (no_cover_or_compl_of_induced_rookThree grid s t X Y).2.false iso
  · rintro (⟨s, t, h⟩ | ⟨s, t, X, Y, h⟩)
    · rcases h with h | h
      · obtain ⟨iso⟩ := h
        exact (no_clique_union_or_compl_of_induced_five_cycle cycle s t).1.false iso
      · obtain ⟨iso⟩ := h
        exact (no_clique_union_or_compl_of_induced_five_cycle cycle s t).2.false iso
    · rcases h with h | h
      · obtain ⟨iso⟩ := h
        exact (no_cover_or_compl_of_induced_five_cycle cycle s t X Y).1.false iso
      · obtain ⟨iso⟩ := h
        exact (no_cover_or_compl_of_induced_five_cycle cycle s t X Y).2.false iso

end EPPAIII.Primitive
