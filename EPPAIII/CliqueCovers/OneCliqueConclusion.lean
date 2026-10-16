import EPPAIII.CliqueCovers.OneCliqueDuality
import EPPAIII.CliqueCovers.ActualHostConclusion
import EPPAIII.EPPA.ComplementTransport

/-!
# The single-clique selected half, s=1

The complement of K_t is an independent t-set. Relabel that
complement as tK_1, use the verified independent-base cover
classification, and complement the entire host again.
The index-transposition lemma shows that all resulting cross
relations are the four allowed diagonal types.
No exterior clique-partition assumption is required here.
-/

namespace EPPAIII.CliqueCovers

/-- Complementing a graph commutes with pulling it back along
a bijection. The irreflexive graph complement is used. -/
theorem complement_comap_equiv {U W : Type*}
    (H : SimpleGraph W) (φ : U ≃ W) :
    (Hᶜ).comap φ = (H.comap φ)ᶜ := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  simp [SimpleGraph.compl_adj, φ.injective.eq_iff]

/-- Every double-sized transitive EPPA witness of one K_t has one
of the four generalized clique-cover connections. The witness need
not be imprimitive and its complementary half need not be given
in advance. The normal-form equivalence fixes the selected K_t. -/
theorem eppa_one_clique_double_classification {t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 1 × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 1 t) H e)
    (ht : 0 < t)
    (hOrder : Fintype.card W = 2 * t)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ (φ : CoverVertex 1 t ≃ W) (X : CrossType),
      (∀ x : Fin 1 × Fin t, φ (false,x) = e x) ∧
      H.comap φ = coverGraph 1 t X false := by
  classical
  let ρ : (Fin t × Fin 1) ≃ (Fin 1 × Fin t) :=
    oneCliqueBaseSwap t
  let e' : (Fin t × Fin 1) ↪ W := EPPAIII.relabelEmbedding e ρ
  have hComp : IsEPPAEmbedding
      (cliqueUnion 1 t)ᶜ Hᶜ e :=
    EPPAIII.eppa_embedding_complement
      (cliqueUnion 1 t) H e heppa
  have heppa' : IsEPPAEmbedding (cliqueUnion t 1) Hᶜ e' :=
    EPPAIII.eppa_relabel_base
      (cliqueUnion 1 t)ᶜ Hᶜ e hComp ρ
      (cliqueUnion t 1) (oneCliqueBaseSwap_complement t)
  have hTrans' : HasTransitiveGraphAutomorphisms Hᶜ :=
    EPPAIII.BlockSystems.transitive_complement H hTransitive
  have hDouble : Fintype.card W = 2 * t * 1 := by
    simpa using hOrder
  obtain ⟨outside,hOutside⟩ :=
    outside_of_transitive_one_vertex_cliques
      Hᶜ e' heppa'.1 ht hDouble hTrans'
  obtain ⟨ψ,X,Y,hFix,hGraph⟩ :=
    eppa_independent_double_classification
      Hᶜ e' heppa' ht hOrder hTrans' outside hOutside
  let κ : CoverVertex 1 t ≃ CoverVertex t 1 :=
    oneCliqueIndexSwap t
  let φ : CoverVertex 1 t ≃ W := κ.trans ψ
  have hBottom (x : Fin 1 × Fin t) :
      φ (false,x) = e x := by
    change ψ (false,(x.2,x.1)) = e x
    simpa [e',EPPAIII.relabelEmbedding,ρ,oneCliqueBaseSwap] using
      hFix (x.2,x.1)
  have hComap : (Hᶜ).comap φ =
      (coverGraph t 1 X Y).comap κ := by
    apply SimpleGraph.ext
    funext u v
    apply propext
    change ((Hᶜ).comap ψ).Adj (κ u) (κ v) ↔
      (coverGraph t 1 X Y).Adj (κ u) (κ v)
    rw [hGraph]
  have hCompComap : (H.comap φ)ᶜ =
      (coverGraph t 1 X Y).comap κ := by
    rw [←complement_comap_equiv H φ]
    exact hComap
  have hAfter : H.comap φ =
      ((coverGraph t 1 X Y).comap κ)ᶜ := by
    have h := congrArg
      (fun F : SimpleGraph (CoverVertex 1 t) => Fᶜ) hCompComap
    simpa using h
  have hSwapComp :
      ((coverGraph t 1 X Y).comap κ)ᶜ =
        ((coverGraph t 1 X Y)ᶜ).comap κ :=
    (complement_comap_equiv (coverGraph t 1 X Y) κ).symm
  refine ⟨φ,oneCliqueDualCrossType X Y,hBottom,?_⟩
  exact hAfter.trans (hSwapComp.trans
    (oneCliqueDualCoverGraph t X Y))

end EPPAIII.CliqueCovers
