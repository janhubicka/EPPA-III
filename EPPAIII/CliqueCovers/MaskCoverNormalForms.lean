import EPPAIII.CliqueCovers.MaskCoverDegree

/-!
# The four full/empty cross-block patterns are generalised clique covers

Once the zero-partial outside masks have been put in one of their
four symmetric-group normal forms, no further graph-theoretic
argument is necessary: the corresponding graph is literally a
uniform generalised clique cover.

The four possibilities are all-empty, all-full, singleton masks
(one complete diagonal cross block per class), and co-singleton
masks (empty diagonal and all off-diagonal blocks complete).
The checks below hold for all s,t, including degenerate values.
-/

namespace EPPAIII.CliqueCovers

/-- No cross edge: the disjoint union of the two sK_t halves. -/
theorem maskCoverGraph_empty_eq_coverGraph (s t : ℕ) :
    maskCoverGraph s t (fun _ => ∅) = coverGraph s t .empty false := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy <;>
    simp [maskCoverGraph,maskCoverAdj,coverGraph,coverAdj,
      CrossType.rel,eq_comm,ne_comm]

/-- Every cross-block is complete. -/
theorem maskCoverGraph_full_eq_coverGraph (s t : ℕ) :
    maskCoverGraph s t
      (fun _ => (Finset.univ : Finset (Fin s))) =
        coverGraph s t .full true := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy <;>
    simp [maskCoverGraph,maskCoverAdj,coverGraph,coverAdj,
      CrossType.rel,eq_comm,ne_comm]

/-- Each outside class meets only the corresponding base clique,
and does so completely. -/
theorem maskCoverGraph_singleton_eq_coverGraph (s t : ℕ) :
    maskCoverGraph s t (fun j => ({j} : Finset (Fin s))) =
      coverGraph s t .full false := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy <;>
    simp [maskCoverGraph,maskCoverAdj,coverGraph,coverAdj,
      CrossType.rel,eq_comm,ne_comm]

/-- Each outside class meets every base clique except its
corresponding one, with complete off-diagonal blocks. -/
theorem maskCoverGraph_cosingleton_eq_coverGraph (s t : ℕ) :
    maskCoverGraph s t
      (fun j => (Finset.univ : Finset (Fin s)).erase j) =
        coverGraph s t .empty true := by
  apply SimpleGraph.ext
  funext x y
  apply propext
  rcases x with ⟨bx,⟨i,a⟩⟩
  rcases y with ⟨cy,⟨j,b⟩⟩
  cases bx <;> cases cy <;>
    simp [maskCoverGraph,maskCoverAdj,coverGraph,coverAdj,
      CrossType.rel,eq_comm,ne_comm]

end EPPAIII.CliqueCovers
