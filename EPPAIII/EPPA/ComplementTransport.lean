import EPPAIII.BlockSystems.TransitiveSeparatedHalf

/-!
# Complement transport of graph EPPA embeddings

For simple undirected graphs, a partial isomorphism is also a
partial isomorphism of the complement, and conversely. The same
full host automorphism preserves the complemented adjacency.
Therefore EPPA of a fixed induced embedding G -> H transfers
without any new witness or coherent choice of extensions to
the embedding of G-complement into H-complement.

This is the formal bridge needed whenever a Section 3 proof
says to pass to graph complements. It keeps separate the
distinction between complementing both graphs and attempting
to complement the host alone.
-/

namespace EPPAIII

/-- Any partial automorphism of the complement is a partial
automorphism of the original simple graph. Distinctness of
domain vertices is preserved by the permutation. -/
theorem partial_complement_implies_original
    {V : Type*} (G : SimpleGraph V)
    (D : Finset V) (p : Equiv.Perm V)
    (h : IsPartialGraphAutomorphism Gᶜ D p) :
    IsPartialGraphAutomorphism G D p := by
  classical
  intro u v hu hv
  by_cases huv : u = v
  · subst v
    simp
  · have hpne : p u ≠ p v := p.injective.ne huv
    have hNeg : (¬ G.Adj u v) ↔ ¬ G.Adj (p u) (p v) := by
      have hh := h u v hu hv
      change (u ≠ v ∧ ¬ G.Adj u v) ↔
        (p u ≠ p v ∧ ¬ G.Adj (p u) (p v)) at hh
      constructor
      · intro hNo
        exact (hh.mp ⟨huv,hNo⟩).2
      · intro hNo
        exact (hh.mpr ⟨hpne,hNo⟩).2
    constructor
    · intro hAdj
      by_contra hNot
      exact (hNeg.mpr hNot) hAdj
    · intro hAdj
      by_contra hNot
      exact (hNeg.mp hNot) hAdj

/-- Every partial automorphism of G is a partial
automorphism of its complement. -/
theorem partial_original_implies_complement
    {V : Type*} (G : SimpleGraph V)
    (D : Finset V) (p : Equiv.Perm V)
    (h : IsPartialGraphAutomorphism G D p) :
    IsPartialGraphAutomorphism Gᶜ D p := by
  intro u v hu hv
  change (u ≠ v ∧ ¬ G.Adj u v) ↔
    (p u ≠ p v ∧ ¬ G.Adj (p u) (p v))
  constructor
  · rintro ⟨hne,hNo⟩
    refine ⟨p.injective.ne hne,?_⟩
    intro hAdj
    exact hNo ((h u v hu hv).mpr hAdj)
  · rintro ⟨hne,hNo⟩
    refine ⟨fun hEq => hne (congrArg p hEq),?_⟩
    intro hAdj
    exact hNo ((h u v hu hv).mp hAdj)

/-- Complementing the selected graph and the witness preserves
the exact EPPA property of the designated induced embedding.
No new witness or coherent family of lifts is required. -/
theorem eppa_embedding_complement
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) :
    IsEPPAEmbedding Gᶜ Hᶜ e := by
  constructor
  · exact BlockSystems.induced_embedding_complement G H e heppa.1
  · intro D p hPartial
    have hOriginal :=
      partial_complement_implies_original G D p hPartial
    obtain ⟨q,hq,hRestrict⟩ := heppa.2 D p hOriginal
    exact ⟨q,BlockSystems.graphAutomorphism_complement H q hq,
      hRestrict⟩

end EPPAIII
