import EPPAIII.BlockSystems.CycleFiveEmptyFullConclusion
import EPPAIII.EPPA.BaseRelabel
import EPPAIII.EPPA.ComplementTransport

/-!
# Exact complementation of a selected C5 EPPA embedding

The five-cycle is self-complementary via multiplication by two
on Fin 5. Complement the actual EPPA host AND selected base,
then reindex the base by this permutation. The result is again
a genuine EPPA embedding of C5 into the complemented host.

This is the graph-theoretic half of the degree reduction
k ↦ 5-k in current Lemma 6.12.
-/

namespace EPPAIII.BlockSystems

/-- The explicit cyclic index switches C5 with its complement
in both directions. -/
theorem cycleFiveComplementIndex_comap_back :
    (SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex =
      SimpleGraph.cycleGraph 5 := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  have h : ∀ a b : Fin 5,
      (SimpleGraph.cycleGraph 5)ᶜ.Adj
        (cycleFiveDoubleIndex a) (cycleFiveDoubleIndex b) ↔
      (SimpleGraph.cycleGraph 5).Adj a b := by
    decide
  exact h x y

/-- The complemented host, with the distinguished copy of
C5 reindexed, still has the full extension property. -/
theorem cycleFive_complement_reindexed_eppa
    {W : Type*} (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e) :
    IsEPPAEmbedding (SimpleGraph.cycleGraph 5) Hᶜ
      (EPPAIII.relabelEmbedding e cycleFiveDoubleIndex) := by
  have hc : IsEPPAEmbedding (SimpleGraph.cycleGraph 5)ᶜ Hᶜ e :=
    EPPAIII.eppa_embedding_complement
      (SimpleGraph.cycleGraph 5) H e heppa
  apply EPPAIII.eppa_relabel_base
    (SimpleGraph.cycleGraph 5)ᶜ Hᶜ e hc
    cycleFiveDoubleIndex (SimpleGraph.cycleGraph 5)
  intro x y
  change (SimpleGraph.cycleGraph 5).Adj x y ↔
    ((SimpleGraph.cycleGraph 5)ᶜ.comap cycleFiveDoubleIndex).Adj x y
  rw [cycleFiveComplementIndex_comap_back]

end EPPAIII.BlockSystems
