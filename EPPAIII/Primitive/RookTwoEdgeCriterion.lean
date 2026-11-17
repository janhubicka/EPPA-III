import EPPAIII.Primitive.RookCoordinateExtension
import EPPAIII.Primitive.RookObstruction

/-!
# Exact criterion for EPPA in a square rook graph

Induced matchings of two edges have a common neighbour exactly when
their directions differ. This gives the obstruction corresponding to
the positive coordinate-extension criterion.
-/

namespace EPPAIII.Primitive

private abbrev RookMatchCell (n : ℕ) := Fin n × Fin n

private theorem matching_common_neighbour {n : ℕ} {a b c d : RookMatchCell n}
    (h : RookInducedMatching a b c d) :
    (∃ x, (rookGraph n).Adj x a ∧ (rookGraph n).Adj x b ∧
      (rookGraph n).Adj x c ∧ (rookGraph n).Adj x d) ↔
    ¬ rookSameDirection a b c d := by
  obtain ⟨hab, hcd, eac, ead, ebc, ebd, hac, had, hbc, hbd⟩ := h
  constructor
  · rintro ⟨x, hxa, hxb, hxc, hxd⟩ hDir
    simp only [rookSameDirection, rookGraph, ne_eq, Prod.ext_iff] at *
    grind
  · intro hDir
    by_cases hR : a.1 = b.1
    · refine ⟨(a.1, c.2), ?_⟩
      simp only [rookSameDirection, rookGraph, ne_eq, Prod.ext_iff] at *
      grind
    · refine ⟨(c.1, a.2), ?_⟩
      simp only [rookSameDirection, rookGraph, ne_eq, Prod.ext_iff] at *
      grind

/-- A chosen set of cells contains a same-direction or opposite-direction
induced matching, as specified by a proposition. -/
def rookHasMatchingDirection {n : ℕ} (S : Set (RookMatchCell n)) (direction : Prop) : Prop :=
  ∃ a b c d : S, RookInducedMatching a.val b.val c.val d.val ∧
    (rookSameDirection a.val b.val c.val d.val ↔ direction)

private theorem rookGraph_not_eppa_of_conflicting_matchings {n : ℕ} (S : Set (RookMatchCell n))
    (hSame : rookHasMatchingDirection S True) (hOpposite : rookHasMatchingDirection S False) :
    ¬ IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n) (Function.Embedding.subtype S) := by
  classical
  obtain ⟨a, b, c, d, hA, hSame⟩ := hSame
  obtain ⟨e, f, g, h, hB, hOpposite⟩ := hOpposite
  let u : Fin 4 → S := ![a, b, c, d]
  let v : Fin 4 → S := ![e, f, g, h]
  have tuple {a b c d : RookMatchCell n} (h : RookInducedMatching a b c d) :
      TwoEdgeTuple (rookGraph n) ![a, b, c, d] := by
    obtain ⟨hab, hcd, _, _, _, _, hac, had, hbc, hbd⟩ := h
    exact four_cells_match (rookGraph n) hab hcd hac had hbc hbd
  have hUMap : (fun i => (u i).val) = ![a.val, b.val, c.val, d.val] := by
    funext i
    fin_cases i <;> rfl
  have hVMap : (fun i => (v i).val) = ![e.val, f.val, g.val, h.val] := by
    funext i
    fin_cases i <;> rfl
  refine not_eppa_of_twoEdgeTuples (rookGraph n) S u v ?_ ?_ ?_ ?_
  · rw [hUMap]
    exact tuple hA
  · rw [hVMap]
    exact tuple hB
  · rintro ⟨x, hx⟩
    exact (matching_common_neighbour hA).mp
      ⟨x, hx 0, hx 1, hx 2, hx 3⟩ (hSame.mpr trivial)
  · obtain ⟨x, hx⟩ := (matching_common_neighbour hB).mpr hOpposite.mp
    refine ⟨x, fun i => ?_⟩
    fin_cases i
    · exact hx.1
    · exact hx.2.1
    · exact hx.2.2.1
    · exact hx.2.2.2

/-- A selected rook subgraph is EPPA exactly when it does not contain
both directions of induced two-edge matching. -/
theorem rookGraph_eppa_iff_no_conflicting_matchings {n : ℕ} (S : Set (RookMatchCell n)) :
    IsEPPAEmbedding ((rookGraph n).induce S) (rookGraph n) (Function.Embedding.subtype S) ↔
      ¬ (rookHasMatchingDirection S True ∧ rookHasMatchingDirection S False) := by
  refine ⟨fun hEppa h => rookGraph_not_eppa_of_conflicting_matchings S h.1 h.2 hEppa, ?_⟩
  classical
  intro hNo
  by_cases hSame : rookHasMatchingDirection S True
  · apply rookGraph_eppa_of_matchingDirection S True
    intro a b c d hA
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    by_contra hOpp
    exact hNo ⟨hSame, a, b, c, d, hA, ⟨hOpp, False.elim⟩⟩
  · apply rookGraph_eppa_of_matchingDirection S False
    intro a b c d hA
    exact ⟨fun h => hSame ⟨a, b, c, d, hA, ⟨fun _ => trivial, fun _ => h⟩⟩, False.elim⟩

end EPPAIII.Primitive
