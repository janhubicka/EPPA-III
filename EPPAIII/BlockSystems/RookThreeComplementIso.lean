import EPPAIII.BlockSystems.RookThreeBase

/-!
# An explicit self-complementing permutation of the 3×3 rook graph

The invertible linear change of coordinates
 (x,y) ↦ (x+y,x−y) over Fin 3 exchanges shared-row/column edges
and opposite-row/opposite-column nonedges. Thus the rook graph
is self-complementary; its alternative outside realization needs
no appeal to a classification of strongly regular graphs.

The finite inverse and adjacency calculation are Lean kernel checks.
-/

namespace EPPAIII.BlockSystems

/-- The concrete 9-point bijection that exchanges rook edges and
rook nonedges. -/
def rookComplementIndex : (Fin 3 × Fin 3) ≃ (Fin 3 × Fin 3) :=
  Equiv.ofBijective
    (fun x : Fin 3 × Fin 3 => (x.1 + x.2, x.1 - x.2))
    (by decide)

/-- Every rook edge becomes a rook nonedge and conversely. -/
theorem rookComplementIndex_adj :
    ∀ u v : Fin 3 × Fin 3,
      rookThreeGraph.Adj (rookComplementIndex u) (rookComplementIndex v) ↔
        rookThreeGraphᶜ.Adj u v := by
  decide

/-- The simple-graph complement of R3 is isomorphic to R3. -/
theorem rookComplementIndex_comap :
    rookThreeGraph.comap rookComplementIndex = rookThreeGraphᶜ := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  exact rookComplementIndex_adj u v


/-- The same concrete index map also transports the complementary
rook graph back to the original rook graph. -/
theorem rookComplementIndex_comap_back :
    rookThreeGraphᶜ.comap rookComplementIndex = rookThreeGraph := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  decide

end EPPAIII.BlockSystems
