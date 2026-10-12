import EPPAIII.CliqueCovers.TwinQuotientCount
import EPPAIII.CliqueCovers.SelectedTwinIndependent
import EPPAIII.CliqueCovers.RegularGraphIndependent
import EPPAIII.CliqueCovers.TransitiveHalfEdges
import EPPAIII.CliqueCovers.TwinQuotientArithmetic
import EPPAIII.CliqueCovers.TwinQuotientAction
import EPPAIII.CliqueCovers.TwinClassSize

/-!
# Zero-partial-profile witnesses have twin classes of exact size t

This is the main counting step of the direct Lemma 3.7 proof.

Let H have 2st vertices, contain an induced sK_t, and have no
partial outside-neighbourhood coordinate. The selected cliques lie
inside distinct true-twin classes, each of size at least t.
If H is vertex-transitive, its closed-twin quotient is transitive,
and all twin classes have a common size a. When the quotient has at
least one edge, it is a positive-degree regular graph. The selected
classes form an independent set of size s, so the verified
independent-set theorem gives 2s ≤ |Q|. Finally

  |Q|*a = 2st,     a≥t,     2s≤|Q|

forces |Q|=2s and a=t.

The hypothesis that the quotient has an edge is kept explicit:
excluding the edgeless quotient by non-homogeneity is a separate
structural lemma, not silently assumed here.
-/

namespace EPPAIII.CliqueCovers

/-- Under vertex-transitivity, zero partial coordinates, and an
edge in the twin quotient, the quotient has exactly 2s classes
and each selected true-twin class has cardinality t. -/
theorem zero_partial_exact_twin_class_size {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (he : IsInducedGraphEmbedding (cliqueUnion s t) H e)
    (hNoPartial : ∀ w : W, w ∉ Set.range e →
      ∀ j : Fin s,
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = 0 ∨
        (profileSlice (finiteNeighbourhoodProfile H e w) j).card = t)
    (hs : 0 < s) (ht : 0 < t)
    (hHostCard : Fintype.card W = 2 * s * t)
    (hTransitive : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        EPPAIII.IsGraphAutomorphism H q ∧ q u = v)
    [Fintype (ClosedTwinQuotient H)]
    [DecidableRel (closedTwinQuotientGraph H).Adj]
    (hPositive : ∃ x y : ClosedTwinQuotient H,
      (closedTwinQuotientGraph H).Adj x y)
    (i : Fin s) (a : Fin t) :
    Fintype.card (ClosedTwinQuotient H) = 2 * s ∧
      (closedTwinClass H (e (i,a))).card = t := by
  classical
  let Q : SimpleGraph (ClosedTwinQuotient H) :=
    closedTwinQuotientGraph H
  haveI : Nonempty (ClosedTwinQuotient H) :=
    ⟨Quotient.mk (closedTwinSetoid H) (e (i,a))⟩
  have hQTrans : HasTransitiveGraphAutomorphisms Q :=
    closedTwinQuotient_transitive H hTransitive
  obtain ⟨d,hReg⟩ := regular_of_transitive_graph Q hQTrans
  have hd : 0 < d := by
    obtain ⟨x,y,hxy⟩ := hPositive
    have hx : 0 < Q.degree x :=
      (Q.degree_pos_iff_exists_adj x).mpr ⟨y,hxy⟩
    simpa [hReg x] using hx
  have hInd :
      Q.IsIndepSet
        (selectedTwinClasses H e a : Set (ClosedTwinQuotient H)) :=
    selectedTwinClasses_independent H e he a
  have hHalf :
      2 * (selectedTwinClasses H e a).card ≤
        Fintype.card (ClosedTwinQuotient H) :=
    regular_graph_independent_card_le_half
      Q d hd hReg (selectedTwinClasses H e a) hInd
  have hMlower : 2 * s ≤ Fintype.card (ClosedTwinQuotient H) := by
    simpa [selectedTwinClasses_card H e he a] using hHalf
  have hAtLeast :
      t ≤ (closedTwinClass H (e (i,a))).card :=
    selected_clique_card_le_twin_class H e he hNoPartial i a
  have hFiberCard :
      Fintype.card (ClosedTwinQuotient H) *
        (closedTwinClass H (e (i,a))).card = 2 * s * t := by
    calc
      _ = Fintype.card W :=
        closedTwinQuotient_card_mul_class_of_transitive
          H hTransitive (e (i,a))
      _ = 2 * s * t := hHostCard
  exact twin_quotient_numerical_rigidity
    s t (closedTwinClass H (e (i,a))).card
    (Fintype.card (ClosedTwinQuotient H))
    hs ht hAtLeast hFiberCard hMlower

end EPPAIII.CliqueCovers
