import EPPAIII.BlockSystems.CycleFiveEmptyFullConclusion
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# The separated C5 double in actual ten-vertex EPPA hosts

The existing theorem constructs the complementary induced C5
without an imprimitive-partition assumption. If outside vertices
have no neighbours in the selected five-cycle, the entire host is
the disjoint union of two cycles. The equivalence fixes the
designated selected copy pointwise.

No outside action, coherence, or finite graph classification is used.
-/

namespace EPPAIII.BlockSystems

/-- Canonical graph comprising two disconnected five-cycles. -/
def cycleFiveDisjointDoubleGraph : SimpleGraph (Bool × Fin 5) where
  Adj u v := u.1 = v.1 ∧
    (SimpleGraph.cycleGraph 5).Adj u.2 v.2
  symm := by
    constructor
    intro u v h
    exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact (SimpleGraph.cycleGraph 5).irrefl h.2

/-- An actual ten-vertex transitive EPPA witness of an induced
C5 with no cross-edges is exactly two disjoint copies of C5,
under an equivalence fixing the selected copy. -/
theorem cycleFive_eppa_zero_cross_host_is_two_cycles
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 5) ↪ W)
    (heppa : IsEPPAEmbedding (SimpleGraph.cycleGraph 5) H e)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hTen : Fintype.card W = 10)
    (hZero : ∀ w : W, w ∈ finiteOutside e →
      (finiteNeighbourhoodProfile H e w).card = 0) :
    ∃ φ : Bool × Fin 5 ≃ W,
      (∀ x : Fin 5, φ (false,x) = e x) ∧
      H.comap φ = cycleFiveDisjointDoubleGraph := by
  classical
  obtain ⟨f,hTop⟩ :=
    cycleFive_eppa_outside_is_cycle H e heppa hTrans hTen
  let φ : Bool × Fin 5 ≃ W :=
    CliqueCovers.balancedHostEquiv e f
  have hSeparated (w : W) (hw : w ∈ finiteOutside e)
      (x : Fin 5) : ¬ H.Adj w (e x) := by
    intro hadj
    have hx : x ∈ finiteNeighbourhoodProfile H e w := by
      simpa [finiteNeighbourhoodProfile] using hadj
    have hEmpty := Finset.card_eq_zero.mp (hZero w hw)
    rw [hEmpty] at hx
    simpa using hx
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
        (false = false ∧ (SimpleGraph.cycleGraph 5).Adj x y)
      simpa using (heppa.1 x y).symm
    · change H.Adj (e x) (f y).val ↔
        (false = true ∧ (SimpleGraph.cycleGraph 5).Adj x y)
      simp only [Bool.false_eq_true,false_and,iff_false]
      intro h
      exact hSeparated (f y).val (f y).property x h.symm
    · change H.Adj (f x).val (e y) ↔
        (true = false ∧ (SimpleGraph.cycleGraph 5).Adj x y)
      simp only [Bool.true_eq_false,false_and,iff_false]
      intro h
      exact hSeparated (f x).val (f x).property y h
    · change H.Adj (f x).val (f y).val ↔
        (true = true ∧ (SimpleGraph.cycleGraph 5).Adj x y)
      have hh : (H.comap (fun z => (f z).val)).Adj x y ↔
          (SimpleGraph.cycleGraph 5).Adj x y := by rw [hTop]
      simpa using hh

end EPPAIII.BlockSystems
