import EPPAIII.BlockSystems.RookThreeSingletonOutside
import EPPAIII.BlockSystems.RookThreeHostDoubleIdentification

/-!
# Explicit matching hosts of the exceptional nine-vertex rook graph

With one actual singleton outside profile, the previous result
canonically labels the nine outside vertices by their unique
selected rook neighbour. The cross graph is an actual matching,
while the top graph is the rook graph or its complement.
We identify the *entire* host through an equivalence fixing
the selected rook graph, not a conjectured outside coordinate
system or a coherent action of EPPA extensions.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Matching rook double: both halves induce the rook graph,
or the upper half its complement, with corresponding mate edges. -/
def rookMatchingRelation (topComplement : Bool)
    (u v : Bool × rookVertex) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then rookThreeGraph.Adj u.2 v.2
    else if topComplement then
      u.2 ≠ v.2 ∧ ¬ rookThreeGraph.Adj u.2 v.2
    else rookThreeGraph.Adj u.2 v.2
  else u.2 = v.2

instance (topComplement : Bool) :
    DecidableRel (rookMatchingRelation topComplement) := by
  intro u v
  unfold rookMatchingRelation
  infer_instance

def rookMatchingGraph (topComplement : Bool) :
    SimpleGraph (Bool × rookVertex) :=
  SimpleGraph.fromRel (rookMatchingRelation topComplement)

instance (topComplement : Bool) :
    DecidableRel (rookMatchingGraph topComplement).Adj := by
  intro u v
  change Decidable (u ≠ v ∧
    (rookMatchingRelation topComplement u v ∨
      rookMatchingRelation topComplement v u))
  infer_instance

/-- This displayed relation is already symmetric and loopless. -/
theorem rookMatchingGraph_adj_iff :
    ∀ topComplement : Bool, ∀ u v : Bool × rookVertex,
      (rookMatchingGraph topComplement).Adj u v ↔
        rookMatchingRelation topComplement u v := by
  decide

/-- Four layer restrictions uniquely determine the matching model. -/
theorem rookMatchingGraph_eq_of_layers
    (J : SimpleGraph (Bool × rookVertex))
    (topComplement : Bool)
    (hBB : ∀ x y : rookVertex,
      J.Adj (false,x) (false,y) ↔ rookThreeGraph.Adj x y)
    (hTT : ∀ x y : rookVertex,
      J.Adj (true,x) (true,y) ↔
        (if topComplement then x ≠ y ∧ ¬ rookThreeGraph.Adj x y
         else rookThreeGraph.Adj x y))
    (hBT : ∀ x y : rookVertex,
      J.Adj (false,x) (true,y) ↔ x = y)
    (hTB : ∀ x y : rookVertex,
      J.Adj (true,x) (false,y) ↔ x = y) :
    J = rookMatchingGraph topComplement := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  cases b <;> cases c
  · rw [rookMatchingGraph_adj_iff]
    simpa [rookMatchingRelation] using hBB x y
  · rw [rookMatchingGraph_adj_iff]
    simpa [rookMatchingRelation] using hBT x y
  · rw [rookMatchingGraph_adj_iff]
    simpa [rookMatchingRelation] using hTB x y
  · rw [rookMatchingGraph_adj_iff]
    simpa [rookMatchingRelation] using hTT x y

/-- Once the nine outside singleton labels have been constructed,
the induced rook/anti-rook top alternatives determine the whole
actual host as one of the two canonical matching models. -/
theorem rook_actual_singleton_host_eq_matching_graph
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : rookVertex ↪ W)
    (he : IsInducedGraphEmbedding rookThreeGraph H e)
    (f : rookVertex ≃ {w : W // w ∈ finiteOutside e})
    (hProfiles : ∀ x : rookVertex,
      finiteNeighbourhoodProfile H e (f x).val = {x})
    (hTop :
      H.comap (fun x => (f x).val) = rookThreeGraph ∨
      H.comap (fun x => (f x).val) = rookThreeGraphᶜ) :
    ∃ topComplement : Bool,
      H.comap (CliqueCovers.balancedHostEquiv e f) =
        rookMatchingGraph topComplement := by
  classical
  have hCross (x y : rookVertex) :
      H.Adj (e x) (f y).val ↔ x = y := by
    rw [rook_cross_edge_iff_profile_member H e (f y).val x,
        hProfiles y]
    simp
  let phi := CliqueCovers.balancedHostEquiv e f
  let J : SimpleGraph (Bool × rookVertex) := H.comap phi
  have hBB (x y : rookVertex) :
      J.Adj (false,x) (false,y) ↔ rookThreeGraph.Adj x y := by
    simpa [J,phi] using (he x y).symm
  have hBT (x y : rookVertex) :
      J.Adj (false,x) (true,y) ↔ x = y := by
    simpa [J,phi] using hCross x y
  have hTB (x y : rookVertex) :
      J.Adj (true,x) (false,y) ↔ x = y := by
    have hSym : H.Adj (f x).val (e y) ↔
        H.Adj (e y) (f x).val := H.adj_comm _ _
    simpa [J,phi,eq_comm] using (hSym.trans (hCross y x))
  rcases hTop with hRook | hComplement
  · refine ⟨false,?_⟩
    apply rookMatchingGraph_eq_of_layers J false hBB ?_ hBT hTB
    intro x y
    have h : (H.comap (fun x => (f x).val)).Adj x y ↔
        rookThreeGraph.Adj x y := by rw [hRook]
    simpa [J,phi] using h
  · refine ⟨true,?_⟩
    apply rookMatchingGraph_eq_of_layers J true hBB ?_ hBT hTB
    intro x y
    have h : (H.comap (fun x => (f x).val)).Adj x y ↔
        rookThreeGraphᶜ.Adj x y := by rw [hComplement]
    simpa [J,phi,SimpleGraph.compl_adj] using h

/-- One outside singleton already classifies the whole actual
eighteen-vertex transitive R3 EPPA witness into two explicit
matching graph models, fixing the designated selected copy. -/
theorem rook_eppa_singleton_host_two_matching_graphs
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (h18 : Fintype.card W = 18)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ (phi : Bool × rookVertex ≃ W) (topComplement : Bool),
      (∀ x : rookVertex, phi (false,x) = e x) ∧
      H.comap phi = rookMatchingGraph topComplement := by
  classical
  obtain ⟨f,hProfiles,hTop⟩ :=
    rook_eppa_singleton_outside_graph_two_forms
      H e heppa hTrans h18 w hw hOne
  obtain ⟨topComplement,hGraph⟩ :=
    rook_actual_singleton_host_eq_matching_graph
      H e heppa.1 f hProfiles hTop
  let phi := CliqueCovers.balancedHostEquiv e f
  refine ⟨phi,topComplement,?_,hGraph⟩
  intro x
  exact CliqueCovers.balancedHostEquiv_false e f x

end EPPAIII.BlockSystems
