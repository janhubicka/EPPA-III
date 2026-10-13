import EPPAIII.CliqueCovers.ZeroPartialNoncluster
import EPPAIII.CliqueCovers.OutsideTwinClasses

/-!
# The remaining quotient classes give exactly s outside clique slots

The zero-partial counting theorem shows that in a non-cluster
vertex-transitive host of order 2st, the quotient by closed twins
contains exactly 2s classes. Precisely s of them come from the
distinguished sK_t, and all of these have size t.

Thus the quotient classes not meeting the distinguished copy form
a finite set of cardinality exactly s. This is the natural indexing
budget for the full-coordinate mask-orbit argument; no choice of
outside labels or graph isomorphism is assumed.
-/

namespace EPPAIII.CliqueCovers

/-- The unselected closed-neighbourhood classes in the quotient. -/
noncomputable def outsideTwinQuotientClasses {s t : ℕ}
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (a : Fin t) [Fintype (ClosedTwinQuotient H)] :
    Finset (ClosedTwinQuotient H) := by
  classical
  exact (Finset.univ : Finset (ClosedTwinQuotient H)) \
    selectedTwinClasses H e a

/-- Exactly s of the 2s quotient classes remain after removing
the selected classes. -/
theorem outsideTwinQuotientClasses_card {s t : ℕ}
    {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (a : Fin t) [Fintype (ClosedTwinQuotient H)]
    (hCount : Fintype.card (ClosedTwinQuotient H) = 2 * s) :
    (outsideTwinQuotientClasses H e a).card = s := by
  classical
  have hSelected : (selectedTwinClasses H e a).card = s :=
    selectedTwinClasses_card H e he a
  unfold outsideTwinQuotientClasses
  rw [Finset.card_sdiff]
  simp only [Finset.univ_inter, Finset.card_univ]
  rw [hSelected, hCount]
  omega

end EPPAIII.CliqueCovers
