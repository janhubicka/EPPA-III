import EPPAIII.BlockSystems.OccupiedBlockAction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected components are uniformly sized in a vertex-transitive graph

For an actual graph automorphism q, reachability is preserved in
both directions. Therefore q transports the finite set of vertices
reachable from u bijectively onto the set reachable from q(u).
If the graph is vertex-transitive, all these connected components
have equal numbers of vertices.

This invariant supplies the last non-numerical ingredient in the
Case-1 perfect-matching reduction of unequal-clique Lemma 3.12.
It makes no assumption of connectedness or EPPA.
-/

namespace EPPAIII.BlockSystems

/-- Every actual graph automorphism determines a graph homomorphism. -/
def graphAutomorphismHom {W : Type*}
    (J : SimpleGraph W) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism J q) : J →g J where
  toFun := q
  map_rel' := by
    intro u v huv
    exact (hq u v).mp huv

/-- Reachability is invariant under a genuine graph automorphism. -/
theorem graphAutomorphism_reachable_iff {W : Type*}
    (J : SimpleGraph W) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism J q) (u v : W) :
    J.Reachable (q u) (q v) ↔ J.Reachable u v := by
  have hInv : IsGraphAutomorphism J q.symm := by
    intro a b
    simpa using (hq (q.symm a) (q.symm b)).symm
  constructor
  · intro huv
    have h : J.Reachable (q.symm (q u)) (q.symm (q v)) :=
      huv.map (graphAutomorphismHom J q.symm hInv)
    simpa only [q.symm_apply_apply] using h
  · intro huv
    exact huv.map (graphAutomorphismHom J q hq)

/-- Finite set of all vertices in the connected component of u. -/
noncomputable def reachableVertices {W : Type*}
    [Fintype W] (J : SimpleGraph W) (u : W) : Finset W := by
  classical
  exact Finset.univ.filter (fun v => J.Reachable u v)

/-- Automorphisms take the complete connected component of u to
the complete connected component of q(u). -/
theorem reachableVertices_image_aut {W : Type*}
    [Fintype W] [DecidableEq W]
    (J : SimpleGraph W) (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism J q) (u : W) :
    (reachableVertices J u).image q = reachableVertices J (q u) := by
  classical
  ext w
  simp only [reachableVertices, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v,hv,hvw⟩
    rw [← hvw]
    exact (graphAutomorphism_reachable_iff J q hq u v).mpr hv
  · intro hw
    have hPre : J.Reachable u (q.symm w) :=
      (graphAutomorphism_reachable_iff J q hq u (q.symm w)).mp
        (by simpa using hw)
    exact ⟨q.symm w, hPre, by simp⟩

/-- Every vertex-transitive finite graph has equally large
connected components, whether or not the graph is connected. -/
theorem transitive_connected_component_card_eq {W : Type*}
    [Fintype W]
    (J : SimpleGraph W)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms J)
    (u v : W) :
    (reachableVertices J u).card = (reachableVertices J v).card := by
  classical
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  calc
    (reachableVertices J u).card =
        ((reachableVertices J u).image q).card :=
      (Finset.card_image_of_injective _ q.injective).symm
    _ = (reachableVertices J (q u)).card :=
      congrArg Finset.card (reachableVertices_image_aut J q hq u)
    _ = (reachableVertices J v).card := by rw [hqu]

end EPPAIII.BlockSystems
