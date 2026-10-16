import EPPAIII.BlockSystems.CycleFiveSingletonOutside
import EPPAIII.BlockSystems.CycleFiveDoubleClassification

/-!
# Two explicit matching hosts of a selected C5

The outside labels come from actual unique singleton profiles,
not from a prior outside matching or a coherent choice of lifts.
With these labels, the graph is one of two explicit two-layer
matching models (prism or Petersen), according to the top graph.
Primitivity of the Petersen model is a separate obligation.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

def cycleFiveMatchingRelation (topComplement : Bool)
    (u v : Bool × Fin 5) : Prop :=
  if u.1 = v.1 then
    if u.1 = false then cycleFiveExplicitAdjacent u.2 v.2
    else if topComplement then
      u.2 ≠ v.2 ∧ ¬ cycleFiveExplicitAdjacent u.2 v.2
    else cycleFiveExplicitAdjacent u.2 v.2
  else u.2 = v.2

instance (topComplement : Bool) :
    DecidableRel (cycleFiveMatchingRelation topComplement) := by
  intro u v
  unfold cycleFiveMatchingRelation
  infer_instance

def cycleFiveMatchingGraph (topComplement : Bool) :
    SimpleGraph (Bool × Fin 5) :=
  SimpleGraph.fromRel (cycleFiveMatchingRelation topComplement)

instance (topComplement : Bool) :
    DecidableRel (cycleFiveMatchingGraph topComplement).Adj := by
  intro u v
  change Decidable (u ≠ v ∧
    (cycleFiveMatchingRelation topComplement u v ∨
     cycleFiveMatchingRelation topComplement v u))
  infer_instance

/-- The displayed adjacency is already symmetric and loopless. -/
theorem cycleFiveMatchingGraph_adj_iff :
    ∀ topComplement : Bool,
      ∀ u v : Bool × Fin 5,
        (cycleFiveMatchingGraph topComplement).Adj u v ↔
          cycleFiveMatchingRelation topComplement u v := by
  decide

/-- The restrictions to the four pairs of layers determine the graph. -/
theorem cycleFiveMatchingGraph_eq_of_layers
    (J : SimpleGraph (Bool × Fin 5))
    (topComplement : Bool)
    (hBB : ∀ x y : Fin 5,
      J.Adj (false,x) (false,y) ↔
        (SimpleGraph.cycleGraph 5).Adj x y)
    (hTT : ∀ x y : Fin 5,
      J.Adj (true,x) (true,y) ↔
        (if topComplement then
           x ≠ y ∧ ¬ (SimpleGraph.cycleGraph 5).Adj x y
         else (SimpleGraph.cycleGraph 5).Adj x y))
    (hBT : ∀ x y : Fin 5,
      J.Adj (false,x) (true,y) ↔ x = y)
    (hTB : ∀ x y : Fin 5,
      J.Adj (true,x) (false,y) ↔ x = y) :
    J = cycleFiveMatchingGraph topComplement := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  cases b <;> cases c
  · rw [cycleFiveMatchingGraph_adj_iff]
    simpa [cycleFiveMatchingRelation, cycleFiveExplicitAdjacent_iff] using hBB x y
  · rw [cycleFiveMatchingGraph_adj_iff]
    simpa [cycleFiveMatchingRelation] using hBT x y
  · rw [cycleFiveMatchingGraph_adj_iff]
    simpa [cycleFiveMatchingRelation] using hTB x y
  · rw [cycleFiveMatchingGraph_adj_iff]
    simpa [cycleFiveMatchingRelation, cycleFiveExplicitAdjacent_iff] using hTT x y

/-- The actual host is one of the two matching models under
the equivalence constructed from its singleton profiles. -/
theorem cycleFive_actual_singleton_host_eq_matching_graph
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin 5) ↪ W)
    (he : IsInducedGraphEmbedding (SimpleGraph.cycleGraph 5) H e)
    (f : Fin 5 ≃ {w : W // w ∈ finiteOutside e})
    (hProfiles : ∀ x : Fin 5,
      finiteNeighbourhoodProfile H e (f x).val = {x})
    (hTop :
      H.comap (fun x => (f x).val) = SimpleGraph.cycleGraph 5 ∨
      H.comap (fun x => (f x).val) =
        (SimpleGraph.cycleGraph 5)ᶜ) :
    ∃ topComplement : Bool,
      H.comap (CliqueCovers.balancedHostEquiv e f) =
        cycleFiveMatchingGraph topComplement := by
  classical
  have hCross (x y : Fin 5) :
      H.Adj (e x) (f y).val ↔ x = y := by
    rw [cycleFive_cross_iff_profile_member H e (f y).val x,
        hProfiles y]
    simp
  let phi := CliqueCovers.balancedHostEquiv e f
  let J : SimpleGraph (Bool × Fin 5) := H.comap phi
  have hBB (x y : Fin 5) :
      J.Adj (false,x) (false,y) ↔
        (SimpleGraph.cycleGraph 5).Adj x y := by
    simpa [J,phi] using (he x y).symm
  have hBT (x y : Fin 5) :
      J.Adj (false,x) (true,y) ↔ x = y := by
    simpa [J,phi] using hCross x y
  have hTB (x y : Fin 5) :
      J.Adj (true,x) (false,y) ↔ x = y := by
    have hSym : H.Adj (f x).val (e y) ↔
        H.Adj (e y) (f x).val := H.adj_comm _ _
    simpa [J,phi,eq_comm] using (hSym.trans (hCross y x))
  rcases hTop with hCycle | hComplement
  · refine ⟨false,?_⟩
    apply cycleFiveMatchingGraph_eq_of_layers J false hBB ?_ hBT hTB
    intro x y
    have h : (H.comap (fun x => (f x).val)).Adj x y ↔
        (SimpleGraph.cycleGraph 5).Adj x y := by rw [hCycle]
    simpa [J,phi] using h
  · refine ⟨true,?_⟩
    apply cycleFiveMatchingGraph_eq_of_layers J true hBB ?_ hBT hTB
    intro x y
    have h : (H.comap (fun x => (f x).val)).Adj x y ↔
        (SimpleGraph.cycleGraph 5)ᶜ.Adj x y := by rw [hComplement]
    simpa [J,phi,SimpleGraph.compl_adj] using h

/-- Full host classification with only one outside singleton
profile and actual host vertex transitivity. -/
theorem cycleFive_eppa_singleton_host_two_matching_graphs
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (w : W) (hw : w ∈ finiteOutside e)
    (hOne : (finiteNeighbourhoodProfile H e w).card = 1) :
    ∃ (phi : Bool × Fin 5 ≃ W) (topComplement : Bool),
      (∀ x : Fin 5, phi (false,x) = e x) ∧
      H.comap phi = cycleFiveMatchingGraph topComplement := by
  classical
  obtain ⟨f,hProfiles,hTop⟩ :=
    cycleFive_eppa_singleton_outside_graph_two_forms
      H e heppa hTrans hTen w hw hOne
  obtain ⟨topComplement,hGraph⟩ :=
    cycleFive_actual_singleton_host_eq_matching_graph
      H e heppa.1 f hProfiles hTop
  let phi := CliqueCovers.balancedHostEquiv e f
  refine ⟨phi,topComplement,?_,hGraph⟩
  intro x
  exact CliqueCovers.balancedHostEquiv_false e f x

end EPPAIII.BlockSystems
