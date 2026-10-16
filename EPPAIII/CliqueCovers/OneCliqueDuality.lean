import EPPAIII.CliqueCovers.Basic
import EPPAIII.EPPA.BaseRelabel

/-!
# Complementing an independent-base clique cover

A graph on two independent layers, indexed as t copies of K_1,
becomes after complementation a graph on two cliques of size t.
The cross relation is complete/empty/matching/co-matching.
The equivalence below interchanges the block and within-block
indices without changing the selected side.
-/

namespace EPPAIII.CliqueCovers

/-- Convert the diagonal and off-diagonal connection bits of an
independent-base cover to the single cross type of a clique-base cover. -/
def oneCliqueDualCrossType (X : CrossType) (Y : Bool) : CrossType :=
  match X, Y with
  | .empty, false => .full
  | .coMatching, false => .full
  | .full, false => .coMatching
  | .matching, false => .coMatching
  | .empty, true => .matching
  | .coMatching, true => .matching
  | .full, true => .empty
  | .matching, true => .empty

def oneCliqueIndexSwap (t : ℕ) : CoverVertex 1 t ≃ CoverVertex t 1 where
  toFun x := (x.1,(x.2.2,x.2.1))
  invFun x := (x.1,(x.2.2,x.2.1))
  left_inv := by
    rintro ⟨b,⟨i,a⟩⟩
    rfl
  right_inv := by
    rintro ⟨b,⟨a,i⟩⟩
    rfl

def oneCliqueBaseSwap (t : ℕ) :
    (Fin t × Fin 1) ≃ (Fin 1 × Fin t) where
  toFun x := (x.2,x.1)
  invFun x := (x.2,x.1)
  left_inv := by
    rintro ⟨a,i⟩
    rfl
  right_inv := by
    rintro ⟨i,a⟩
    rfl

/-- The standard independent tK_1 is the relabelled complement
of the complete graph 1K_t. -/
theorem oneCliqueBaseSwap_complement (t : ℕ)
    (x y : Fin t × Fin 1) :
    (cliqueUnion t 1).Adj x y ↔
      (cliqueUnion 1 t)ᶜ.Adj
        (oneCliqueBaseSwap t x) (oneCliqueBaseSwap t y) := by
  simp [cliqueUnion_one_right_eq_bot,
    cliqueUnion_one_left_eq_top, SimpleGraph.compl_adj]

/-- The graph-level conversion is exact, including all vertices
and both internal layers. -/
theorem oneCliqueDualCoverGraph (t : ℕ) (X : CrossType) (Y : Bool) :
    ((coverGraph t 1 X Y)ᶜ).comap (oneCliqueIndexSwap t) =
      coverGraph 1 t (oneCliqueDualCrossType X Y) false := by
  classical
  apply SimpleGraph.ext
  funext u v
  apply propext
  rcases u with ⟨bu,⟨i,a⟩⟩
  rcases v with ⟨bv,⟨j,b⟩⟩
  have hij : i = j := Subsingleton.elim i j
  subst j
  cases bu <;> cases bv <;> cases X <;> cases Y <;>
    by_cases h : a = b <;>
    simp [oneCliqueIndexSwap,oneCliqueDualCrossType,
      coverGraph,coverAdj,SimpleGraph.compl_adj,
      CrossType.rel,h,Prod.mk.injEq]

end EPPAIII.CliqueCovers
