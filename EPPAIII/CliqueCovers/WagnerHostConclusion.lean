import EPPAIII.CliqueCovers.WagnerOutsideMatching

/-!
# Full eight-vertex Wagner witness in the exceptional double-partial case

The selected half is an induced 2K₂. In the two-partial saturated
orbit every outside vertex has one neighbour in each designated K₂,
labelled by its two chosen points. The other four vertices induce
the opposite-corner matching by the outside graph theorem.

The canonical eight-vertex graph below records precisely these
three kinds of edges. The final theorem identifies the *entire*
vertex-transitive EPPA host with this graph, using the original
base embedding and canonical outside labels. It neither assumes a
partition of the outside half nor chooses a coherent system of
extensions.

The coordinate graph is the Wagner graph (the 8-vertex Möbius ladder)
in the labelling natural to its selected 2K₂.
-/

namespace EPPAIII.CliqueCovers

/-- The canonical eight-vertex model: two selected K₂ edges,
two opposite-corner outside edges, and two selected neighbours
for every outside vertex. -/
def wagnerCanonicalAdj (x y : CoverVertex 2 2) : Prop :=
  (x.1 = false ∧ y.1 = false ∧
    x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 = true ∧ y.1 = true ∧
    x.2.1 ≠ y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 = false ∧ y.1 = true ∧
    (if x.2.1 = (0 : Fin 2) then x.2.2 = y.2.1
      else x.2.2 = y.2.2)) ∨
  (x.1 = true ∧ y.1 = false ∧
    (if y.2.1 = (0 : Fin 2) then y.2.2 = x.2.1
      else y.2.2 = x.2.2))

/-- The explicit Wagner model is a simple graph. -/
def wagnerCanonicalGraph : SimpleGraph (CoverVertex 2 2) where
  Adj := wagnerCanonicalAdj
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hx,hy,hi,ha⟩ | ⟨hx,hy,hi,ha⟩ |
      ⟨hx,hy,hcross⟩ | ⟨hx,hy,hcross⟩
    · exact Or.inl ⟨hy,hx,hi.symm,ha.symm⟩
    · exact Or.inr (Or.inl ⟨hy,hx,hi.symm,ha.symm⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hy,hx,hcross⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hy,hx,hcross⟩))
  loopless := by
    constructor
    intro x h
    rcases h with ⟨_,_,_,ha⟩ | ⟨_,_,hi,_⟩ |
      ⟨hf,ht,_⟩ | ⟨ht,hf,_⟩
    · exact ha rfl
    · exact hi rfl
    · exact Bool.false_ne_true (hf.symm.trans ht)
    · exact Bool.false_ne_true (hf.symm.trans ht)

/-- At each selected base vertex, the incidence with a canonically
labelled outside corner is specified by the selected point in the
corresponding one of the two coordinates. -/
theorem saturatedWagner_cross_iff
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (x : Bool × Bool) (i : Fin 2) (a : Fin 2) :
    H.Adj (saturatedWagnerOutsideEquiv H e heppa
        hOrder w hw hBoth x).val (e (i,a)) ↔
      if i = (0 : Fin 2) then a = finTwoEquiv.symm x.1
      else a = finTwoEquiv.symm x.2 := by
  classical
  fin_cases i
  · have hMem :
        H.Adj (saturatedWagnerOutsideEquiv H e heppa
          hOrder w hw hBoth x).val (e ((0 : Fin 2),a)) ↔
          a ∈ profileSlice (finiteNeighbourhoodProfile H e
            (saturatedWagnerOutsideEquiv H e heppa
              hOrder w hw hBoth x).val) (0 : Fin 2) := by
      simp [profileSlice, finiteNeighbourhoodProfile]
    rw [saturatedWagnerOutsideEquiv_first H e heppa hOrder
      w hw hBoth x] at hMem
    simpa using hMem
  · have hMem :
        H.Adj (saturatedWagnerOutsideEquiv H e heppa
          hOrder w hw hBoth x).val (e ((1 : Fin 2),a)) ↔
          a ∈ profileSlice (finiteNeighbourhoodProfile H e
            (saturatedWagnerOutsideEquiv H e heppa
              hOrder w hw hBoth x).val) (1 : Fin 2) := by
      simp [profileSlice, finiteNeighbourhoodProfile]
    rw [saturatedWagnerOutsideEquiv_second H e heppa hOrder
      w hw hBoth x] at hMem
    simpa using hMem

/-- The whole host in the two-partial case is the explicit
eight-vertex Wagner graph, not merely a graph with the right
outside orbit cardinality. -/
theorem eppa_two_partial_host_is_wagner_fixed_base
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ phi : CoverVertex 2 2 ≃ W,
      (∀ x : Fin 2 × Fin 2, phi (false,x) = e x) ∧
      H.comap phi = wagnerCanonicalGraph := by
  classical
  let rho : (Fin 2 × Fin 2) ≃ Bool × Bool :=
    Equiv.prodCongr finTwoEquiv finTwoEquiv
  let outside := saturatedWagnerOutsideEquiv
    H e heppa hOrder w hw hBoth
  let outsideFin : (Fin 2 × Fin 2) ≃
      {u : W // u ∈ finiteOutside e} := rho.trans outside
  let phi : CoverVertex 2 2 ≃ W := balancedHostEquiv e outsideFin
  have hOut := eppa_wagner_outside_is_opposite_matching
    H e heppa hOrder w hw hBoth hTransitive
  refine ⟨phi, ?_, ?_⟩
  · intro x
    exact balancedHostEquiv_false e outsideFin x
  · apply SimpleGraph.ext
    funext x y
    apply propext
    rcases x with ⟨bx,⟨i,a⟩⟩
    rcases y with ⟨cy,⟨j,c⟩⟩
    cases bx <;> cases cy
    · change H.Adj (e (i,a)) (e (j,c)) ↔
        wagnerCanonicalAdj (false,(i,a)) (false,(j,c))
      simpa [wagnerCanonicalAdj,cliqueUnion] using
        (heppa.1 (i,a) (j,c)).symm
    · change H.Adj (e (i,a)) (outside (rho (j,c))).val ↔
        wagnerCanonicalAdj (false,(i,a)) (true,(j,c))
      have hCross := saturatedWagner_cross_iff
        H e heppa hOrder w hw hBoth (rho (j,c)) i a
      have hSym :
          H.Adj (e (i,a)) (outside (rho (j,c))).val ↔
            H.Adj (outside (rho (j,c))).val (e (i,a)) :=
        H.adj_comm _ _
      simpa [wagnerCanonicalAdj,rho] using hSym.trans hCross
    · change H.Adj (outside (rho (i,a))).val (e (j,c)) ↔
        wagnerCanonicalAdj (true,(i,a)) (false,(j,c))
      have hCross := saturatedWagner_cross_iff
        H e heppa hOrder w hw hBoth (rho (i,a)) j c
      simpa [wagnerCanonicalAdj,rho] using hCross
    · change
        H.Adj (outside (rho (i,a))).val
          (outside (rho (j,c))).val ↔
        wagnerCanonicalAdj (true,(i,a)) (true,(j,c))
      have hB :
          H.Adj (outside (rho (i,a))).val
            (outside (rho (j,c))).val ↔
          (squareCornerGraph false true).Adj (rho (i,a)) (rho (j,c)) := by
        change ((outsideInducedGraph H e).comap outside).Adj
          (rho (i,a)) (rho (j,c)) ↔
          (squareCornerGraph false true).Adj (rho (i,a)) (rho (j,c))
        rw [hOut]
      simpa [wagnerCanonicalAdj,squareCornerGraph,
        squareCornerAdj,rho] using hB

/-- Previously exported Wagner theorem, derived from the aligned model. -/
theorem eppa_two_partial_host_is_wagner
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : (Fin 2 × Fin 2) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion 2 2) H e)
    (hOrder : Fintype.card W = 2 * 2 * 2)
    (w : W) (hw : w ∉ Set.range e)
    (hBoth : (kPositions (finiteNeighbourhoodProfile H e w) 1).card = 2)
    (hTransitive : HasTransitiveGraphAutomorphisms H) :
    ∃ phi : CoverVertex 2 2 ≃ W,
      H.comap phi = wagnerCanonicalGraph := by
  obtain ⟨phi,_,hEq⟩ :=
    eppa_two_partial_host_is_wagner_fixed_base
      H e heppa hOrder w hw hBoth hTransitive
  exact ⟨phi,hEq⟩

end EPPAIII.CliqueCovers
