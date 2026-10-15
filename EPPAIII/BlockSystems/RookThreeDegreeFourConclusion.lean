import EPPAIII.BlockSystems.RookThreeOutsideEquiv
import EPPAIII.BlockSystems.RookThreeOutsideEqualEdges
import EPPAIII.BlockSystems.RookThreeHostDoubleIdentification
import EPPAIII.BlockSystems.RookThreeTriangleCertificates

/-!
# The complete graph-level R3 conclusion when the cross-degree is four

Let H be an 18-vertex vertex-transitive EPPA witness for the induced
nine-vertex rook graph R3, with every outside vertex having four
neighbours in the selected R3. The earlier orbit-multiplicity theorem
constructs canonical outside labels by the rook open neighbourhoods
or strict nonneighbourhoods.

Actual EPPA lifts force the canonically labelled outside graph to
be invariant under the rook automorphism group. Equal half-edge
counts give that this graph is R3 or its complement. The explicit
four-layer adjacency theorem then identifies the entire host with
one of four canonical rook doubles. Finally the verified unequal
ordered-triangle counts exclude the two doubles with complementary
outside rook graph.

The result constructs the equivalence Bool × R3 ≃ H. No coherent
lifts, presumed outside partition, or numerical triangle-count
equations are hypotheses. The remaining exceptional Lemma 3.20
obligations are to derive uniform outside cross-degree four from
the actual host hypotheses, and identify its stated alternatives.
-/

namespace EPPAIII.BlockSystems

/-- An actual 18-vertex vertex-transitive EPPA host of R3 with
outside cross-degree four is one of two explicit rook doubles,
under an equivalence that fixes the designated bottom copy. -/
theorem rook_eppa_degree_four_host_is_rook_double
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (h18 : Fintype.card W = 18)
    (hDegree : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 4) :
    ∃ (φ : Bool × rookVertex ≃ W) (crossNonrook : Bool),
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDoubleGraph false crossNonrook := by
  classical
  obtain ⟨f,hLabels⟩ :=
    rook_eppa_degree_four_outside_equiv H e heppa h18 hDegree
  have hInjective : Set.InjOn
      (finiteNeighbourhoodProfile H e) (finiteOutside e : Set W) :=
    (rook_eppa_degree_four_outside_profile_orbit
      H e heppa h18 hDegree).2
  have hTop :
      H.comap (fun x => (f x).val) = rookThreeGraph ∨
        H.comap (fun x => (f x).val) = rookThreeGraphᶜ :=
    rook_canonical_outside_graph_two_forms
      H e heppa hTrans f hInjective hLabels
  obtain ⟨topComplement,crossNonrook,hGraph⟩ :=
    rook_actual_host_eq_canonical_double
      H e heppa.1 f hTop hLabels
  let φ : Bool × rookVertex ≃ W :=
    CliqueCovers.balancedHostEquiv e f
  have hTransPullback : IsVertexTransitive (H.comap φ) :=
    CliqueCovers.transitive_comap_equiv H φ hTrans
  have hTopIsRook : topComplement = false := by
    cases topComplement with
    | false => rfl
    | true =>
        have hBad : IsVertexTransitive
            (rookDoubleGraph true crossNonrook) := by
          rw [← hGraph]
          exact hTransPullback
        exact False.elim
          (rookDouble_complement_top_not_transitive crossNonrook hBad)
  refine ⟨φ,crossNonrook,?_,?_⟩
  · intro x
    exact CliqueCovers.balancedHostEquiv_false e f x
  · simpa only [hTopIsRook] using hGraph

end EPPAIII.BlockSystems
