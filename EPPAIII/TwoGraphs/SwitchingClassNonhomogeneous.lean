import EPPAIII.TwoGraphs.TransversalParity

/-!
# A non-homogeneous member of every switching class of order at least three

This is the source-facing missing implication (2) -> (1) in the
Section 5 four-way two-graph theorem. The proof needs no classification
of homogeneous two-graphs or finite groups.

Switch at the neighbourhood of one vertex, making that vertex isolated.
If an edge remains, the graph is not vertex-transitive. Otherwise the
result is empty, and switching at the isolated vertex produces a star,
which is not vertex-transitive on at least three vertices.

The final result is phrased with three pairwise distinct vertices rather
than an auxiliary cardinality inequality. It applies to infinite sets too.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.DoubleCover

/-- Homogeneity implies vertex-transitivity: apply the extension
property to the map on a singleton. -/
theorem homogeneous_graph_maps_vertex
    {V : Type*} [DecidableEq V]
    (J : SimpleGraph V)
    (hHom : IsHomogeneousGraph J) (x y : V) :
    ∃ σ : Equiv.Perm V,
      IsGraphAutomorphism J σ ∧ σ x = y := by
  classical
  have hPartial : IsPartialGraphAutomorphism J
      ({x} : Finset V) (Equiv.swap x y) := by
    intro a b ha hb
    have ha' : a = x := by simpa using ha
    have hb' : b = x := by simpa using hb
    subst a
    subst b
    constructor
    · intro h
      exact False.elim ((J.ne_of_adj h) rfl)
    · intro h
      exact False.elim ((J.ne_of_adj h) rfl)
  obtain ⟨σ,hσ,hExt⟩ :=
    hHom ({x} : Finset V) (Equiv.swap x y) hPartial
  refine ⟨σ,hσ,?_⟩
  simpa using hExt x (by simp)

/-- A graph with an isolated vertex and at least one edge cannot
be homogeneous. -/
theorem isolated_and_edge_not_homogeneous
    {V : Type*} [DecidableEq V]
    (J : SimpleGraph V) (x a b : V)
    (hIsolated : ∀ v : V, ¬ J.Adj x v)
    (hEdge : J.Adj a b) : ¬ IsHomogeneousGraph J := by
  intro hHom
  obtain ⟨σ,hσ,hσx⟩ :=
    homogeneous_graph_maps_vertex J hHom x a
  have hAdj : J.Adj x (σ.symm b) := by
    apply (hσ x (σ.symm b)).mpr
    simpa [hσx] using hEdge
  exact hIsolated (σ.symm b) hAdj

/-- On a graph whose edges are exactly those through x, the
singleton partial automorphism mapping x to a leaf cannot extend
when the star has at least two distinct leaves. -/
theorem star_not_homogeneous
    {V : Type*} [DecidableEq V]
    (J : SimpleGraph V) (x y z : V)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hStar : ∀ a b : V, J.Adj a b ↔
      a ≠ b ∧ (a = x ∨ b = x)) :
    ¬ IsHomogeneousGraph J := by
  intro hHom
  obtain ⟨σ,hσ,hσx⟩ :=
    homogeneous_graph_maps_vertex J hHom x y
  have hxyEdge : J.Adj x y :=
    (hStar x y).mpr ⟨hxy, Or.inl rfl⟩
  have hxzEdge : J.Adj x z :=
    (hStar x z).mpr ⟨hxz, Or.inl rfl⟩
  have hY : J.Adj y (σ y) := by
    have h := (hσ x y).mp hxyEdge
    simpa [hσx] using h
  have hZ : J.Adj y (σ z) := by
    have h := (hσ x z).mp hxzEdge
    simpa [hσx] using h
  have hσy : σ y = x := by
    rcases (hStar y (σ y)).mp hY with ⟨_, h | h⟩
    · exact False.elim (hxy h.symm)
    · exact h
  have hσz : σ z = x := by
    rcases (hStar y (σ z)).mp hZ with ⟨_, h | h⟩
    · exact False.elim (hxy h.symm)
    · exact h
  exact hyz (σ.injective (hσy.trans hσz.symm))

/-- Switching twice is switching once by the XOR of the two
Boolean side functions. The equality includes loops (both sides
are simple graphs). -/
theorem taylor_transversal_switch_twice
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V → Bool) :
    taylorTransversalGraph (taylorTransversalGraph G s) t =
      taylorTransversalGraph G (fun v => Bool.xor (s v) (t v)) := by
  classical
  apply SimpleGraph.ext
  funext x y
  apply propext
  have hDecision :
      decide ((taylorTransversalGraph
          (taylorTransversalGraph G s) t).Adj x y) =
        decide ((taylorTransversalGraph G
          (fun v => Bool.xor (s v) (t v))).Adj x y) := by
    calc
      decide ((taylorTransversalGraph
          (taylorTransversalGraph G s) t).Adj x y) =
          Bool.xor (decide ((taylorTransversalGraph G s).Adj x y))
            (Bool.xor (t x) (t y)) :=
        taylor_transversal_decide_adj
          (taylorTransversalGraph G s) t x y
      _ = Bool.xor
            (Bool.xor (decide (G.Adj x y)) (Bool.xor (s x) (s y)))
            (Bool.xor (t x) (t y)) := by
        rw [taylor_transversal_decide_adj G s x y]
      _ = Bool.xor (decide (G.Adj x y))
            (Bool.xor (Bool.xor (s x) (t x))
              (Bool.xor (s y) (t y))) := by
        cases hA : decide (G.Adj x y) <;>
          cases hSx : s x <;> cases hSy : s y <;>
          cases hTx : t x <;> cases hTy : t y <;> rfl
      _ = decide ((taylorTransversalGraph G
            (fun v => Bool.xor (s v) (t v))).Adj x y) :=
        (taylor_transversal_decide_adj G
          (fun v => Bool.xor (s v) (t v)) x y).symm
  by_cases hL : (taylorTransversalGraph
      (taylorTransversalGraph G s) t).Adj x y <;>
    by_cases hR : (taylorTransversalGraph G
      (fun v => Bool.xor (s v) (t v))).Adj x y <;>
    simp_all

/-- Seidel-switching at the neighbourhood of x isolates x. -/
theorem taylor_switch_neighbourhood_isolates
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x v : V) :
    ¬ (taylorTransversalGraph G
        (fun z => decide (G.Adj x z))).Adj x v := by
  classical
  have hxx : ¬ G.Adj x x := by
    intro h
    exact (G.ne_of_adj h) rfl
  change ¬ (x ≠ v ∧
    (G.Adj x v ↔
      decide (G.Adj x x) = decide (G.Adj x v)))
  by_cases h : G.Adj x v <;> simp [hxx, h]

/-- Every switching class containing three distinct vertices
has a non-homogeneous representative. In particular this proves
the (2) -> (1) implication of the Section 5 four-way theorem. -/
theorem switching_class_has_nonhomogeneous_representative
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ t : V → Bool,
      ¬ IsHomogeneousGraph (taylorTransversalGraph G t) := by
  classical
  let t₀ : V → Bool := fun v => decide (G.Adj x v)
  let J : SimpleGraph V := taylorTransversalGraph G t₀
  have hIsolated (v : V) : ¬ J.Adj x v :=
    taylor_switch_neighbourhood_isolates G x v
  by_cases hEdge : ∃ a b : V, J.Adj a b
  · obtain ⟨a,b,hab⟩ := hEdge
    exact ⟨t₀, isolated_and_edge_not_homogeneous J x a b hIsolated hab⟩
  · have hEmpty (a b : V) : ¬ J.Adj a b := by
      intro hab
      exact hEdge ⟨a,b,hab⟩
    let t₁ : V → Bool := fun v => if v = x then true else false
    let K : SimpleGraph V := taylorTransversalGraph J t₁
    have hStar (a b : V) :
        K.Adj a b ↔ a ≠ b ∧ (a = x ∨ b = x) := by
      change (a ≠ b ∧ (J.Adj a b ↔ t₁ a = t₁ b)) ↔
        (a ≠ b ∧ (a = x ∨ b = x))
      by_cases hab : a = b
      · subst b
        simp
      · have hn := hEmpty a b
        by_cases hax : a = x <;>
          by_cases hbx : b = x <;>
          simp_all [t₁]
    have hBad : ¬ IsHomogeneousGraph K :=
      star_not_homogeneous K x y z hxy hxz hyz hStar
    let u : V → Bool := fun v => Bool.xor (t₀ v) (t₁ v)
    have hEq : K = taylorTransversalGraph G u := by
      change taylorTransversalGraph
          (taylorTransversalGraph G t₀) t₁ =
        taylorTransversalGraph G
          (fun v => Bool.xor (t₀ v) (t₁ v))
      exact taylor_transversal_switch_twice G t₀ t₁
    refine ⟨u,?_⟩
    rw [← hEq]
    exact hBad

end EPPAIII.TwoGraphs
