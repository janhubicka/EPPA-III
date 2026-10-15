import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# The nine-vertex R3 rook graph

For the exceptional Lemma 3.20 we model R3 as the graph on
Fin 3 × Fin 3 joining distinct points in a common row or column.
This is the 3×3 rook graph, with degree four.

Coordinate translations preserve the graph and act transitively
on the nine vertices. These elementary facts provide a concrete
finite base before the more delicate subset-orbit analysis.
-/

namespace EPPAIII.BlockSystems

/-- The 3×3 rook graph: two distinct vertices share a row or column. -/
def rookThreeGraph : SimpleGraph (Fin 3 × Fin 3) where
  Adj u v := u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)
  symm := by
    constructor
    intro u v
    constructor
    · rintro ⟨hne,h⟩
      exact ⟨hne.symm,h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
    · rintro ⟨hne,h⟩
      exact ⟨hne.symm,h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

instance : DecidableRel rookThreeGraph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2))
  infer_instance

/-- R3 has exactly four neighbours at every vertex. -/
theorem rookThreeGraph_degree_four :
    ∀ u : Fin 3 × Fin 3,
      ((Finset.univ : Finset (Fin 3 × Fin 3)).filter
        (fun v => rookThreeGraph.Adj u v)).card = 4 := by
  decide

/-- Translate the row and column coordinates independently. -/
def rookThreeTranslation (d : Fin 3 × Fin 3) :
    Equiv.Perm (Fin 3 × Fin 3) :=
  Equiv.prodCongr (Equiv.addRight d.1) (Equiv.addRight d.2)

/-- Every row/column translation is an automorphism of R3. -/
theorem rookThree_translation_graph_automorphism
    (d : Fin 3 × Fin 3) :
    IsGraphAutomorphism rookThreeGraph (rookThreeTranslation d) := by
  let q := rookThreeTranslation d
  have hCoordinate (u v : Fin 3 × Fin 3) :
      ((q u).1 = (q v).1 ∨ (q u).2 = (q v).2) ↔
        (u.1 = v.1 ∨ u.2 = v.2) := by
    change (u.1 + d.1 = v.1 + d.1 ∨
      u.2 + d.2 = v.2 + d.2) ↔
        (u.1 = v.1 ∨ u.2 = v.2)
    constructor
    · rintro (h | h)
      · exact Or.inl (add_right_cancel h)
      · exact Or.inr (add_right_cancel h)
    · rintro (h | h)
      · exact Or.inl (congrArg (· + d.1) h)
      · exact Or.inr (congrArg (· + d.2) h)
  intro u v
  change (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)) ↔
    (q u ≠ q v ∧ ((q u).1 = (q v).1 ∨ (q u).2 = (q v).2))
  constructor
  · rintro ⟨hne,h⟩
    exact ⟨q.injective.ne hne,(hCoordinate u v).mpr h⟩
  · rintro ⟨hne,h⟩
    exact ⟨fun huv => hne (congrArg q huv),(hCoordinate u v).mp h⟩

/-- The nine-vertex R3 graph is vertex-transitive. -/
theorem rookThreeGraph_vertex_transitive :
    CliqueCovers.HasTransitiveGraphAutomorphisms rookThreeGraph := by
  intro u v
  let d : Fin 3 × Fin 3 := (v.1 - u.1, v.2 - u.2)
  refine ⟨rookThreeTranslation d,
    rookThree_translation_graph_automorphism d,?_⟩
  apply Prod.ext
  · change u.1 + (v.1 - u.1) = v.1
    abel
  · change u.2 + (v.2 - u.2) = v.2
    abel

end EPPAIII.BlockSystems
