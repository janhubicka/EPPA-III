import EPPAIII.BlockSystems.RookThreeComplementIso
import EPPAIII.BlockSystems.RookThreeSmallSubsetOrbits
import EPPAIII.EPPA.BaseRelabel
import EPPAIII.EPPA.ComplementTransport

/-!
# EPPA transport across complement of the rook graph

The complementary R3 is isomorphic to R3 by the explicit
nine-point permutation (i,j) ↦ (i+j,i−j). The same permutation
reindexes the base EPPA embedding into the graph complement
of the host. This construction keeps the actual selected
vertices, merely changing their labels, and uses no
automorphism classification or coherent EPPA lifts.
-/

namespace EPPAIII.BlockSystems

/-- Complement R3 and the host simultaneously, then relabel
the selected base by the concrete rook complement isomorphism.
The resulting embedding remains a genuine EPPA embedding
of the original rook graph. -/
theorem rook_complement_reindexed_eppa
    {W : Type*}
    (H : SimpleGraph W) (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e) :
    IsEPPAEmbedding rookThreeGraph Hᶜ
      (EPPAIII.relabelEmbedding e rookComplementIndex) := by
  have hComplement : IsEPPAEmbedding rookThreeGraphᶜ Hᶜ e :=
    EPPAIII.eppa_embedding_complement rookThreeGraph H e heppa
  apply EPPAIII.eppa_relabel_base
    rookThreeGraphᶜ Hᶜ e hComplement
      rookComplementIndex rookThreeGraph
  intro x y
  change rookThreeGraph.Adj x y ↔
    (rookThreeGraphᶜ.comap rookComplementIndex).Adj x y
  rw [rookComplementIndex_comap_back]

/-- A relabelling of a selected EPPA copy does not change
the actual set of vertices outside that copy. -/
theorem finiteOutside_relabelEmbedding
    {U V W : Type*} [Fintype W]
    (e : V ↪ W) (p : U ≃ V) :
    finiteOutside (EPPAIII.relabelEmbedding e p) = finiteOutside e := by
  classical
  ext w
  simp only [finiteOutside, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hw ⟨y,hy⟩
    apply hw
    refine ⟨p.symm y,?_⟩
    change e (p (p.symm y)) = w
    simpa using hy
  · intro hw ⟨x,hx⟩
    apply hw
    exact ⟨p x,hx⟩

end EPPAIII.BlockSystems
