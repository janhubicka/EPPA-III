import EPPAIII.BlockSystems.DisjointDoubleNonhomogeneity
import EPPAIII.BlockSystems.ClosedConnectedComponents
import EPPAIII.BlockSystems.TransitivePartition

/-!
# Connected disjoint doubles are genuinely imprimitive

The graph G ⊔ G has a natural two-block partition by the Bool
coordinate. That partition is not generally invariant under
automorphisms if G itself is disconnected. For a preconnected G,
however, its two sides are precisely its graph-theoretic
connected components, so every host automorphism preserves
the block relation.

This is the missing invariant-block certificate for the
disjoint-double examples in Proposition 6.17.
-/

namespace EPPAIII.BlockSystems

/-- In a disjoint double of a preconnected graph, two vertices
are reachable exactly when they lie on the same side. -/
theorem disjoint_double_reachable_iff_same_side
    {V : Type*} (G : SimpleGraph V) (hConn : G.Preconnected)
    (u v : Bool × V) :
    (disjointDoubleGraph G).Reachable u v ↔ u.1 = v.1 := by
  let H := disjointDoubleGraph G
  constructor
  · intro hReach
    let S : Set (Bool × V) := {w | w.1 = u.1}
    have hClosed :
        ∀ a ∈ S, ∀ b : Bool × V,
          H.Adj a b → b ∈ S := by
      intro a ha b hab
      change a.1 = u.1 at ha
      change a.1 = b.1 ∧ G.Adj a.2 b.2 at hab
      change b.1 = u.1
      exact hab.1.symm.trans ha
    have hU : u ∈ S := rfl
    have hV := reachable_mem_of_adj_closed
      H S hClosed u v hU hReach
    change v.1 = u.1 at hV
    exact hV.symm
  · intro hSide
    rcases u with ⟨side,x⟩
    rcases v with ⟨side',y⟩
    change side = side' at hSide
    subst side'
    let ι : G →g disjointDoubleGraph G :=
      { toFun := fun z => (side,z)
        map_rel' := by
          intro a b hab
          exact ⟨rfl,hab⟩ }
    exact (hConn x y).map ι

/-- For a connected base graph the two side blocks form an
Aut(G ⊔ G)-invariant block system; no arbitrary block
invariance is assumed. -/
theorem disjoint_double_invariant_side_blocks
    {V : Type*} (G : SimpleGraph V) (hConn : G.Preconnected) :
    InvariantBlockMap (disjointDoubleGraph G)
      (fun w : Bool × V => w.1) := by
  intro q hq u v
  have hReach := graphAutomorphism_reachable_iff
    (disjointDoubleGraph G) q hq u v
  exact (disjoint_double_reachable_iff_same_side G hConn u v).symm.trans
    (hReach.symm.trans
      (disjoint_double_reachable_iff_same_side G hConn (q u) (q v)))

/-- Both side blocks occur as soon as the base has a vertex. -/
theorem disjoint_double_side_surjective
    {V : Type*} (a : V) :
    Function.Surjective (fun w : Bool × V => w.1) := by
  intro side
  exact ⟨(side,a),rfl⟩

/-- If the base has two distinct vertices, each side block
has at least two vertices. -/
theorem disjoint_double_nontrivial_side_block
    {V : Type*} [Fintype V] [DecidableEq V]
    (a c : V) (hac : a ≠ c) :
    ∃ side : Bool, 2 ≤
      ((Finset.univ : Finset (Bool × V)).filter
        (fun w => w.1 = side)).card := by
  classical
  let S : Finset (Bool × V) := {(false,a),(false,c)}
  have hNe : (false,a) ≠ (false,c) :=
    fun h => hac (congrArg Prod.snd h)
  have hCard : S.card = 2 := by
    simp [S,hNe]
  have hSub :
      S ⊆ (Finset.univ : Finset (Bool × V)).filter
        (fun w => w.1 = false) := by
    intro w hw
    have hw' : w = (false,a) ∨ w = (false,c) := by
      simpa [S] using hw
    rcases hw' with rfl | rfl <;> simp
  refine ⟨false,?_⟩
  calc
    2 = S.card := hCard.symm
    _ ≤ ((Finset.univ : Finset (Bool × V)).filter
      (fun w => w.1 = false)).card :=
        Finset.card_le_card hSub

/-- Complete abstract counterexample schema: if a finite
homogeneous connected base has an induced P3, its disjoint
double is a transitive, non-homogeneous EPPA witness with
a genuine nontrivial invariant two-block partition. -/
theorem disjoint_double_imprimitive_counterexample_schema
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hHom : EPPAIII.DoubleCover.IsHomogeneousGraph G)
    (hConn : G.Preconnected)
    (a b c : V)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hac : a ≠ c)
    (hnot : ¬ G.Adj a c) :
    EPPAIII.IsEPPAEmbedding G (disjointDoubleGraph G)
        (EPPAIII.DoubleCover.bottomEmbedding V) ∧
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
        (disjointDoubleGraph G) ∧
    ¬ EPPAIII.DoubleCover.IsHomogeneousGraph
        (disjointDoubleGraph G) ∧
    InvariantBlockMap (disjointDoubleGraph G)
      (fun w : Bool × V => w.1) ∧
    Function.Surjective (fun w : Bool × V => w.1) ∧
    (∃ side : Bool, 2 ≤
      ((Finset.univ : Finset (Bool × V)).filter
        (fun w => w.1 = side)).card) := by
  obtain ⟨hEPPA,hTrans,hNonhom⟩ :=
    disjoint_double_counterexample_schema
      G hHom a b c hab hbc hac hnot
  exact ⟨hEPPA,hTrans,hNonhom,
    disjoint_double_invariant_side_blocks G hConn,
    disjoint_double_side_surjective a,
    disjoint_double_nontrivial_side_block a c hac⟩

end EPPAIII.BlockSystems
