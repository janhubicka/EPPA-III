import EPPAIII.CliqueCovers.OneCliqueConclusion

/-!
# Complete self-contained classification of generalised clique covers

This statement matches the positive parameters and two induced
clique-union halves in Lemma 6.1 of the reorganised EPPA-III
manuscript. It does not require H to be imprimitive.

All three cases are fully assembled:
* s,t ≥ 2: the fixed-base full double classification;
* t = 1: the independent-base full classification;
* s = 1: the complement-dual single-clique classification.

The graph equivalence fixes the chosen embedded copy of G pointwise.
The Wagner branch uses dependent index casts to express this
without pretending that arbitrary parameters s,t are definitionally 2.
No coherent EPPA extensions or outside partitions are inferred
from an unverified argument.
-/

namespace EPPAIII.CliqueCovers

/-- Exact source-level generalised clique-cover classification.
The image of the designated base graph is preserved pointwise.
This is stronger than Lemma 6.1 in omitting imprimitivity. -/
theorem eppa_all_positive_clique_double_classification
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (outside : (Fin s × Fin t) ≃
      {w : W // w ∈ finiteOutside e})
    (hOutside : (outsideInducedGraph H e).comap outside =
      cliqueUnion s t) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      H.comap phi = coverGraph s t X Y) ∨
    (∃ (hS : s = 2) (hT : t = 2)
        (phi : CoverVertex 2 2 ≃ W),
       (∀ x : Fin 2 × Fin 2,
          phi (false,x) =
            e (Fin.cast hS.symm x.1, Fin.cast hT.symm x.2)) ∧
       H.comap phi = wagnerCanonicalGraph) := by
  classical
  by_cases hS : s = 1
  · subst s
    obtain ⟨phi,X,hFixed,hEq⟩ :=
      eppa_one_clique_double_classification
        H e heppa ht (by simpa using hOrder) hTransitive
    exact Or.inl ⟨phi,X,false,hFixed,hEq⟩
  · have hs2 : 2 ≤ s := by omega
    by_cases hT : t = 1
    · subst t
      obtain ⟨phi,X,Y,hFixed,hEq⟩ :=
        eppa_independent_double_classification
          H e heppa hs (by simpa using hOrder)
          hTransitive outside hOutside
      exact Or.inl ⟨phi,X,Y,hFixed,hEq⟩
    · have ht2 : 2 ≤ t := by omega
      exact eppa_equal_clique_double_classification
        H e heppa hs2 ht2 hOrder
        hTransitive outside hOutside

end EPPAIII.CliqueCovers
