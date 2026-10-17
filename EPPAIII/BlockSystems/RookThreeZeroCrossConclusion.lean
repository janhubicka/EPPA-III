import EPPAIII.BlockSystems.RookThreeMatchingModels
import EPPAIII.BlockSystems.RookThreeDegreeFourConclusion
import EPPAIII.BlockSystems.TransitiveSeparatedHalf

/-!
# R3: the zero-cross-degree host is two disjoint rook graphs

No imprimitivity or outside labelling is assumed. The crucial
graph-theoretic ingredient is connectedness of the nine-vertex
rook graph: an induced connected component occupying half the
host is transported to the complementary half by transitivity.
-/

namespace EPPAIII.BlockSystems

/-- The rook graph has paths of length at most two. -/
theorem rookThreeGraph_preconnected : rookThreeGraph.Preconnected := by
  intro u v
  by_cases heq : u = v
  · subst v
    exact SimpleGraph.Reachable.refl _
  by_cases hadj : rookThreeGraph.Adj u v
  · exact SimpleGraph.Adj.reachable hadj
  have hRow : u.1 ≠ v.1 := by
    intro h
    apply hadj
    exact ⟨heq, Or.inl h⟩
  have hCol : u.2 ≠ v.2 := by
    intro h
    apply hadj
    exact ⟨heq, Or.inr h⟩
  let w : rookVertex := (u.1,v.2)
  have huw : rookThreeGraph.Adj u w := by
    change u ≠ w ∧ (u.1 = w.1 ∨ u.2 = w.2)
    constructor
    · intro h
      exact hCol (by simpa [w] using congrArg Prod.snd h)
    · exact Or.inl rfl
  have hwv : rookThreeGraph.Adj w v := by
    change w ≠ v ∧ (w.1 = v.1 ∨ w.2 = v.2)
    constructor
    · intro h
      exact hRow (by simpa [w] using congrArg Prod.fst h)
    · exact Or.inr rfl
  exact (SimpleGraph.Adj.reachable huw).trans
    (SimpleGraph.Adj.reachable hwv)

/-- A host consisting of two disconnected copies of R3. -/
def rookDisjointDoubleGraph : SimpleGraph (Bool × rookVertex) where
  Adj u v := u.1 = v.1 ∧ rookThreeGraph.Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact rookThreeGraph.irrefl h.2

/-- Actual transitive EPPA host: if the selected R3 has no cross
edges to the outside nine vertices, the whole host is 2R3.
The isomorphism fixes the original selected copy pointwise. -/
theorem rook_eppa_zero_cross_host_is_two_rook_graphs
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : rookVertex ↪ W)
    (heppa : IsEPPAEmbedding rookThreeGraph H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (h18 : Fintype.card W = 18)
    (hZero : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 0) :
    ∃ φ : Bool × rookVertex ≃ W,
      (∀ x : rookVertex, φ (false,x) = e x) ∧
      H.comap φ = rookDisjointDoubleGraph := by
  classical
  have hSeparated : ∀ w : W, w ∈ finiteOutside e →
      ∀ x : rookVertex, ¬ H.Adj w (e x) := by
    intro w hw x h
    have hEmpty : finiteNeighbourhoodProfile H e w = ∅ :=
      Finset.card_eq_zero.mp (hZero w hw)
    have hx : x ∈ finiteNeighbourhoodProfile H e w := by
      simpa [finiteNeighbourhoodProfile] using h
    rw [hEmpty] at hx
    simpa using hx
  have hDouble : Fintype.card W = 2 * Fintype.card rookVertex := by
    simpa using h18
  obtain ⟨f,hTop⟩ :=
    transitive_outside_equiv_of_connected_separated
      rookThreeGraph rookThreeGraph_preconnected
      H e heppa.1 hDouble hTrans hSeparated
  let φ : Bool × rookVertex ≃ W :=
    CliqueCovers.balancedHostEquiv e f
  refine ⟨φ,?_,?_⟩
  · intro x
    exact CliqueCovers.balancedHostEquiv_false e f x
  · apply SimpleGraph.ext
    funext u v
    apply propext
    rcases u with ⟨bu,x⟩
    rcases v with ⟨bv,y⟩
    cases bu <;> cases bv
    · change H.Adj (e x) (e y) ↔
        (false = false ∧ rookThreeGraph.Adj x y)
      simpa using (heppa.1 x y).symm
    · change H.Adj (e x) (f y).val ↔
        (false = true ∧ rookThreeGraph.Adj x y)
      simp only [Bool.false_eq_true, false_and, iff_false]
      intro h
      exact hSeparated (f y).val (f y).property x h.symm
    · change H.Adj (f x).val (e y) ↔
        (true = false ∧ rookThreeGraph.Adj x y)
      simp only [Bool.true_eq_false, false_and, iff_false]
      intro h
      exact hSeparated (f x).val (f x).property y h
    · change H.Adj (f x).val (f y).val ↔
        (true = true ∧ rookThreeGraph.Adj x y)
      have h : (H.comap (fun z => (f z).val)).Adj x y ↔
          rookThreeGraph.Adj x y := by rw [hTop]
      simpa using h

end EPPAIII.BlockSystems
