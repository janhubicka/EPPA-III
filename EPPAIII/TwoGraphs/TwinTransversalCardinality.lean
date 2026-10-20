import EPPAIII.TwoGraphs.TrueTwinTransversalHomogeneity
import EPPAIII.CliqueCovers.TwinQuotientCount

/-!
# One selected representative per true-twin class in a double host

In the second case of Section 5 fibre rigidity, no two selected
vertices belong to one true-twin class. A uniform true-twin class
of at least two vertices, together with a host of twice the
selected order, forces the quotient map of the selected graph
to be bijective. EPPA therefore descends to the quotient and
the base is homogeneous.

This argument uses only finite counting, EPPA, host transitivity
and the canonical true-twin quotient. No Taylor coordinates or
homogeneous-graph classification are needed.
-/

namespace EPPAIII.TwoGraphs

open EPPAIII.CliqueCovers

/-- In an actual double-sized vertex-transitive EPPA host, if
every selected vertex lies in a distinct true-twin class and
the classes have at least two points, then the selected graph
is homogeneous. This completes the quotient-transversal case. -/
theorem double_eppa_separated_twin_classes_homogeneous
    {V W : Type*}
    [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype (ClosedTwinQuotient H)]
    (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hTrans : ∀ u v : W,
      ∃ q : Equiv.Perm W,
        IsGraphAutomorphism H q ∧ q u = v)
    (anchor : V)
    (hClassLarge : 2 ≤ (closedTwinClass H (e anchor)).card)
    (hSeparated : ∀ x y : V,
      SameClosedNeighbourhood H (e x) (e y) → x = y) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  classical
  let Q := ClosedTwinQuotient H
  let π : V → Q := fun x =>
    Quotient.mk (closedTwinSetoid H) (e x)
  have hInj : Function.Injective π := by
    intro x y hxy
    apply hSeparated x y
    exact Quotient.exact hxy
  have hLe : Fintype.card V ≤ Fintype.card Q :=
    Fintype.card_le_of_injective π hInj
  have hCount :
      Fintype.card Q * (closedTwinClass H (e anchor)).card =
        2 * Fintype.card V := by
    calc
      Fintype.card Q * (closedTwinClass H (e anchor)).card =
          Fintype.card W :=
        closedTwinQuotient_card_mul_class_of_transitive H hTrans (e anchor)
      _ = 2 * Fintype.card V := hDouble
  have hTwoLe :
      Fintype.card Q * 2 ≤
        Fintype.card Q * (closedTwinClass H (e anchor)).card :=
    Nat.mul_le_mul_left (Fintype.card Q) hClassLarge
  have hRev : Fintype.card Q ≤ Fintype.card V := by
    omega
  have hCard : Fintype.card V = Fintype.card Q := by
    omega
  have hBij : Function.Bijective π :=
    (Fintype.bijective_iff_injective_and_card π).mpr
      ⟨hInj,hCard⟩
  have hCovered : ∀ w : W,
      ∃ x : V, SameClosedNeighbourhood H w (e x) := by
    intro w
    obtain ⟨x,hx⟩ :=
      hBij.2 (Quotient.mk (closedTwinSetoid H) w)
    have hSame : SameClosedNeighbourhood H (e x) w :=
      Quotient.exact hx
    exact ⟨x,hSame.symm⟩
  exact eppa_twin_transversal_homogeneous
    G H e heppa hCovered hSeparated

end EPPAIII.TwoGraphs
