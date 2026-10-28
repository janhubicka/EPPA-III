import EPPAIII.DoubleCover.TwoPointAction
import EPPAIII.DoubleCover.RigidLayerHomogeneity
import EPPAIII.CliqueCovers.TransitiveHalfEdges
import EPPAIII.BlockSystems.UnequalCase2WithoutHomogeneity

/-!
# Two disjoint copies of a homogeneous graph

The manuscript's final imprimitive summary incorrectly discards
the two-disjoint-copy hosts of the exceptional homogeneous bases
C5 and R3 on the grounds that these hosts are homogeneous.

For ANY finite homogeneous base G, the graph G ⊔ G is an EPPA
witness for the selected first copy. If G is vertex-transitive,
so is G ⊔ G. But if G contains an induced P3, then G ⊔ G is
not homogeneous: within-copy and between-copy nonedge pairs
have different common-neighbour behaviour.

This abstract obstruction requires neither Gardiner's
classification nor enumeration of the automorphism group.
The all-order result explains why the 2G alternatives cannot
be deleted from the final manuscript proposition.
-/

namespace EPPAIII.BlockSystems

/-- Two disjoint induced copies of a graph G, indexed by Bool. -/
def disjointDoubleGraph {V : Type*} (G : SimpleGraph V) :
    SimpleGraph (Bool × V) where
  Adj := fun u v => u.1 = v.1 ∧ G.Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact (G.ne_of_adj h.2) rfl

/-- Whenever G is homogeneous, G ⊔ G is an actual EPPA
witness for its selected bottom copy. -/
theorem disjoint_double_eppa_of_homogeneous
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hHom : EPPAIII.DoubleCover.IsHomogeneousGraph G) :
    EPPAIII.IsEPPAEmbedding G (disjointDoubleGraph G)
      (EPPAIII.DoubleCover.bottomEmbedding V) := by
  classical
  constructor
  · intro x y
    change G.Adj x y ↔
      ((false : Bool) = false ∧ G.Adj x y)
    simp
  · intro D p hp
    obtain ⟨σ,hσ,hFix⟩ := hHom D p hp
    let Q : Equiv.Perm (Bool × V) :=
      Equiv.prodCongr (Equiv.refl Bool) σ
    have hQ : EPPAIII.IsGraphAutomorphism
        (disjointDoubleGraph G) Q := by
      intro u v
      rcases u with ⟨b,x⟩
      rcases v with ⟨c,y⟩
      change (b = c ∧ G.Adj x y) ↔
        (b = c ∧ G.Adj (σ x) (σ y))
      exact and_congr Iff.rfl (hσ x y)
    refine ⟨Q,hQ,?_⟩
    intro x hx
    change (false,σ x) = (false,p x)
    rw [hFix x hx]

/-- The disjoint double of a vertex-transitive graph is
vertex-transitive: freely swap the two copies and transport
within each copy by an actual automorphism of G. -/
theorem disjoint_double_vertex_transitive
    {V : Type*}
    (G : SimpleGraph V)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms G) :
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (disjointDoubleGraph G) := by
  intro u v
  rcases u with ⟨b,x⟩
  rcases v with ⟨c,y⟩
  obtain ⟨σ,hσ,hxy⟩ := hTrans x y
  let τ : Equiv.Perm Bool := Equiv.swap b c
  let Q : Equiv.Perm (Bool × V) := Equiv.prodCongr τ σ
  refine ⟨Q,?_,?_⟩
  · intro u v
    rcases u with ⟨d,x'⟩
    rcases v with ⟨e,y'⟩
    change (d = e ∧ G.Adj x' y') ↔
      (τ d = τ e ∧ G.Adj (σ x') (σ y'))
    have hSides : (d = e) ↔ (τ d = τ e) :=
      ⟨fun heq => congrArg τ heq, fun heq => τ.injective heq⟩
    exact and_congr hSides (hσ x' y')
  · change (τ b,σ x) = (c,y)
    simp [τ,hxy]

/-- An induced P3 in G is an obstruction to homogeneity
of G ⊔ G. The two nonadjacent source vertices share a
neighbour, whereas a pair in different copies never does. -/
theorem disjoint_double_not_homogeneous_of_induced_p3
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (a b c : V)
    (hab : G.Adj a b)
    (hbc : G.Adj b c)
    (hac : a ≠ c)
    (hnot : ¬ G.Adj a c) :
    ¬ EPPAIII.DoubleCover.IsHomogeneousGraph
      (disjointDoubleGraph G) := by
  classical
  let H := disjointDoubleGraph G
  have hType :
      H.Adj (false,a) (false,c) ↔
      H.Adj (false,a) (true,c) := by
    change ((false : Bool) = false ∧ G.Adj a c) ↔
      ((false : Bool) = true ∧ G.Adj a c)
    simp [hnot]
  obtain ⟨p,hpa,hpc,hPart⟩ :=
    EPPAIII.DoubleCover.partial_of_two_maps
      H (false,a) (false,c) (false,a) (true,c)
      (by simpa using hac) (by simp) hType
  intro hHom
  obtain ⟨q,hq,hFix⟩ :=
    hHom ({(false,a),(false,c)} : Finset (Bool × V))
      p hPart
  have hImageA : q (false,a) = (false,a) := by
    calc
      q (false,a) = p (false,a) :=
        hFix (false,a) (by simp)
      _ = (false,a) := hpa
  have hImageC : q (false,c) = (true,c) := by
    calc
      q (false,c) = p (false,c) :=
        hFix (false,c) (by simp)
      _ = (true,c) := hpc
  have hAB : H.Adj (false,a) (false,b) :=
    ⟨rfl,hab⟩
  have hCB : H.Adj (false,c) (false,b) :=
    ⟨rfl,hbc.symm⟩
  have hQAB := (hq (false,a) (false,b)).mp hAB
  have hQCB := (hq (false,c) (false,b)).mp hCB
  rw [hImageA] at hQAB
  rw [hImageC] at hQCB
  rcases hw : q (false,b) with ⟨side,z⟩
  rw [hw] at hQAB hQCB
  have hFalse : side = false := hQAB.1.symm
  have hTrue : side = true := hQCB.1.symm
  exact Bool.false_ne_true (hFalse.symm.trans hTrue)

/-- Abstract counterexample schema: for every homogeneous graph
containing an induced P3, the disjoint double is a
non-homogeneous, vertex-transitive EPPA witness for its
selected copy. -/
theorem disjoint_double_counterexample_schema
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hHom : EPPAIII.DoubleCover.IsHomogeneousGraph G)
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
      (disjointDoubleGraph G) := by
  exact ⟨disjoint_double_eppa_of_homogeneous G hHom,
    disjoint_double_vertex_transitive G
      (homogeneous_graph_vertex_transitive G hHom),
    disjoint_double_not_homogeneous_of_induced_p3
      G a b c hab hbc hac hnot⟩

end EPPAIII.BlockSystems
