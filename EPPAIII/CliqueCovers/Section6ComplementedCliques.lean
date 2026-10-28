import EPPAIII.BlockSystems.Section6NonhomogeneousInterfaces
import EPPAIII.DoubleCover.HomogeneityComplement
import EPPAIII.EPPA.ComplementTransport
import EPPAIII.BlockSystems.TransitiveSeparatedHalf

/-!
# Section 6: complementary equal-clique bases without the double-cover lemma

The final manuscript proposition treats a homogeneous selected
graph which is the complement of a disjoint union of equally sized
cliques. The printed argument invokes the preceding double-cover
lemma for this case, although the lemma explicitly excludes it.

There is no need for that application. Complement the *entire*
EPPA pair (selected graph and host) and use the independently
formalized non-homogeneous equal-clique classification, whose
complementary-half hypothesis has already been eliminated.

This theorem preserves the original selected embedding and gives
a cover/Wagner classification for the complemented host.
Since the manuscript conclusion is explicitly up to
complementation, it provides the missing classification branch
without Gardiner, a rank-three theorem, or coherent EPPA lifts.
-/

namespace EPPAIII.CliqueCovers

/-- Source-facing complemented-clique classification:

If G is the complement of sK_t and H is a non-homogeneous,
vertex-transitive, double-sized EPPA witness for G, then the
complemented host Hᶜ has a generalized-clique-cover model fixing
the original selected vertices, or is the Wagner exception.

No imprimitivity partition or outside-half isomorphism is assumed;
these may be included in the manuscript but are not needed here. -/
theorem eppa_nonhomogeneous_complement_clique_double_all_positive
    {s t : ℕ} {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel Hᶜ.Adj]
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t)ᶜ H e)
    (hs : 0 < s) (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * s * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H)
    (hNonhomogeneous : ¬ EPPAIII.DoubleCover.IsHomogeneousGraph H) :
    (∃ (phi : CoverVertex s t ≃ W) (X : CrossType) (Y : Bool),
      (∀ x : Fin s × Fin t, phi (false,x) = e x) ∧
      Hᶜ.comap phi = coverGraph s t X Y) ∨
    (∃ (hS : s = 2) (hT : t = 2)
        (phi : CoverVertex 2 2 ≃ W),
       (∀ x : Fin 2 × Fin 2,
          phi (false,x) =
            e (Fin.cast hS.symm x.1, Fin.cast hT.symm x.2)) ∧
       Hᶜ.comap phi = wagnerCanonicalGraph) := by
  have hEPPAComplement :
      IsEPPAEmbedding (cliqueUnion s t) Hᶜ e := by
    have hc := EPPAIII.eppa_embedding_complement
      (cliqueUnion s t)ᶜ H e heppa
    simpa using hc
  have hTransitiveComplement :
      HasTransitiveGraphAutomorphisms Hᶜ :=
    EPPAIII.BlockSystems.transitive_complement H hTransitive
  have hNonhomogeneousComplement :
      ¬ EPPAIII.DoubleCover.IsHomogeneousGraph Hᶜ :=
    (EPPAIII.DoubleCover.nonhomogeneous_complement_iff H).mp
      hNonhomogeneous
  exact eppa_nonhomogeneous_clique_double_all_positive
    Hᶜ e hEPPAComplement hs ht hOrder
    hTransitiveComplement hNonhomogeneousComplement

end EPPAIII.CliqueCovers
