import EPPAIII.CliqueCovers.TwinQuotientGraph
import EPPAIII.CliqueCovers.TwinClassSize

/-!
# The selected base cliques form an independent set in the twin quotient

For an induced copy G=sK_t in H, take the canonical closed-neighbourhood
class of one chosen vertex in each selected clique. Since distinct
selected cliques have no edges between them and cannot belong to the
same twin class, these s quotient vertices form an independent set.

No no-partial-profile, host transitivity or EPPA assumption is needed
for this step. It supplies the independent set of size s used with the
positive-degree regular-quotient half bound.
-/

namespace EPPAIII.CliqueCovers

/-- The map taking a clique index to the quotient class of a
chosen vertex inside that clique. -/
def selectedTwinClassMap {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (a : Fin t) : Fin s → ClosedTwinQuotient H :=
  fun i => Quotient.mk (closedTwinSetoid H) (e (i,a))

/-- Distinct selected cliques yield distinct quotient vertices. -/
theorem selectedTwinClassMap_injective {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (a : Fin t) :
    Function.Injective (selectedTwinClassMap H e a) := by
  intro i j hEq
  by_contra hij
  have hSame : SameClosedNeighbourhood H (e (i,a)) (e (j,a)) :=
    Quotient.exact hEq
  exact different_cliques_not_same_closed_neighbourhood
    H e he i j hij a a hSame

/-- The selected quotient vertices, one per clique. -/
noncomputable def selectedTwinClasses {s t : ℕ} {W : Type*}
    (H : SimpleGraph W) (e : (Fin s × Fin t) ↪ W)
    (a : Fin t) : Finset (ClosedTwinQuotient H) := by
  classical
  exact (Finset.univ : Finset (Fin s)).image
    (selectedTwinClassMap H e a)

/-- Exactly s distinct quotient vertices are selected. -/
theorem selectedTwinClasses_card {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (a : Fin t) :
    (selectedTwinClasses H e a).card = s := by
  classical
  unfold selectedTwinClasses
  rw [Finset.card_image_of_injective _
    (selectedTwinClassMap_injective H e he a)]
  simp

/-- The s chosen twin classes are independent in the quotient graph. -/
theorem selectedTwinClasses_independent {s t : ℕ} {W : Type*}
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (a : Fin t) :
    (closedTwinQuotientGraph H).IsIndepSet
      (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) := by
  classical
  intro x hx y hy hxy
  change x ∈ selectedTwinClasses H e a at hx
  change y ∈ selectedTwinClasses H e a at hy
  unfold selectedTwinClasses at hx hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
  have hij : i ≠ j := by
    intro h
    exact hxy (congrArg (selectedTwinClassMap H e a) h)
  have hNoEdge : ¬ H.Adj (e (i,a)) (e (j,a)) := by
    intro h
    exact hij ((he (i,a) (j,a)).mpr h).1
  intro h
  have hAdj :=
    (closedTwinQuotient_adj_mk H (e (i,a)) (e (j,a))).mp h
  exact hNoEdge hAdj.2

end EPPAIII.CliqueCovers
