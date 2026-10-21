import EPPAIII.TwoGraphs.OnePointExtension
import EPPAIII.EPPA.BaseRelabel

/-!
# Reindexing EPPA copies carried by host automorphisms

An automorphic image of the chosen bottom transversal has its
original labels permuted by the induced action on Taylor fibres.
The correct source graph after reindexing is the pullback of G
through the inverse permutation, not necessarily G itself.
This is the source/host interface needed by the one-for-all proof.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- Reindex an automorphic image of the bottom transversal by
its actual fibre indices. -/
def reindexedHostEmbedding {V : Type*}
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V) :
    V ↪ Bool × V :=
  EPPAIII.relabelEmbedding (hostImageEmbedding (bottomEmbedding V) q) σ.symm

/-- The automorphic image, reindexed by its host fibre permutation,
is EPPA for G pulled back by the inverse base permutation. -/
theorem eppa_reindexed_host_image
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (heppa : EPPAIII.IsEPPAEmbedding G (taylorPairGraph G)
      (bottomEmbedding V))
    (q : Equiv.Perm (Bool × V))
    (hq : EPPAIII.IsGraphAutomorphism (taylorPairGraph G) q)
    (σ : Equiv.Perm V) :
    EPPAIII.IsEPPAEmbedding (G.comap σ.symm)
      (taylorPairGraph G) (reindexedHostEmbedding q σ) := by
  exact EPPAIII.eppa_relabel_base G (taylorPairGraph G)
    (hostImageEmbedding (bottomEmbedding V) q)
    (eppa_embedding_of_host_image G (taylorPairGraph G)
      (bottomEmbedding V) heppa q hq)
    σ.symm (G.comap σ.symm) (by intro a b; rfl)

/-- The reindexed embedding really chooses precisely one vertex
from each fibre, indexed by the vertex being embedded. -/
theorem reindexed_host_fibre
    {V : Type*}
    (q : Equiv.Perm (Bool × V))
    (σ : Equiv.Perm V)
    (hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (x : V) :
    (reindexedHostEmbedding q σ x).2 = x := by
  change (q (false,σ.symm x)).2 = x
  rw [hBase false (σ.symm x)]
  simp

/-- Explicitly express a reindexed embedding as the graph of
its Boolean layer-selection function. -/
theorem reindexed_host_choice
    {V : Type*}
    (q : Equiv.Perm (Bool × V))
    (σ : Equiv.Perm V)
    (hBase : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (x : V) :
    reindexedHostEmbedding q σ x =
      ((reindexedHostEmbedding q σ x).1,x) := by
  apply Prod.ext
  · rfl
  · exact reindexed_host_fibre q σ hBase x

/-- Opposite adjacency types to a and b become identical
adjacency types after switching with a layer choice that
separates a and b. -/
theorem taylor_complement_types_equal_on_transversal
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V)
    (t : V → Bool)
    (R : Finset V) (a b : V)
    (ha : a ∉ R) (hb : b ∉ R)
    (hOpp : ∀ r ∈ R, G.Adj a r ↔ ¬ G.Adj b r)
    (hSep : t a ≠ t b) :
    ∀ r ∈ R,
      (taylorPairGraph G).Adj (t a,a) (t r,r) ↔
        (taylorPairGraph G).Adj (t b,b) (t r,r) := by
  intro r hr
  have har : a ≠ r := fun h => ha (h.symm ▸ hr)
  have hbr : b ≠ r := fun h => hb (h.symm ▸ hr)
  have hTypes := hOpp r hr
  change
    (a ≠ r ∧ (G.Adj a r ↔ t a = t r)) ↔
      (b ≠ r ∧ (G.Adj b r ↔ t b = t r))
  cases hta : t a <;> cases htb : t b <;>
    cases htr : t r <;>
    by_cases hA : G.Adj a r <;>
    by_cases hB : G.Adj b r <;>
    simp_all

end EPPAIII.TwoGraphs
