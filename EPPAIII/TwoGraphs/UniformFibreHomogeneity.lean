import EPPAIII.TwoGraphs.HomogeneityTransport
import EPPAIII.CliqueCovers.CliqueUnionHomogeneity

/-!
# Equal-sized clique fibres imply homogeneity

This is the last abstract graph-theoretic interface needed in
the first true-twin quotient case of Section 5 fibre rigidity.

If an arbitrary finite graph is exactly the disjoint union of
equal complete fibres of a finite map, construct an explicit
equivalence with the canonical equal-clique model, then transport
its already verified homogeneity to the original graph.
No EPPA or external classification assumption is used.
-/

namespace EPPAIII.TwoGraphs

/-- A finite graph whose vertices are partitioned into equally sized
complete clique fibres, without edges between different fibres,
is homogeneous. The fibre set may be an arbitrary finite type. -/
theorem homogeneous_of_uniform_complete_fibres
    {V B : Type*} [Fintype V] [Fintype B]
    (G : SimpleGraph V) (f : V → B) (t : ℕ)
    (hCard : ∀ b : B, Fintype.card {v : V // f v = b} = t)
    (hAdj : ∀ x y : V,
      G.Adj x y ↔ f x = f y ∧ x ≠ y) :
    EPPAIII.DoubleCover.IsHomogeneousGraph G := by
  classical
  let eB : Fin (Fintype.card B) ≃ B :=
    (Fintype.equivFin B).symm
  let eFib (b : B) : Fin t ≃ {v : V // f v = b} :=
    (Fintype.equivFinOfCardEq (hCard b)).symm
  let eProd : (B × Fin t) ≃ (Σ _b : B, Fin t) where
    toFun := fun x => ⟨x.1,x.2⟩
    invFun := fun x => (x.1,x.2)
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
  let φ : (Fin (Fintype.card B) × Fin t) ≃ V :=
    (((Equiv.prodCongr eB (Equiv.refl (Fin t))).trans eProd).trans
      (Equiv.sigmaCongrRight eFib)).trans (Equiv.sigmaFiberEquiv f)
  have hMap (x : Fin (Fintype.card B) × Fin t) :
      f (φ x) = eB x.1 := by
    rcases x with ⟨i,a⟩
    change f ((eFib (eB i) a).val) = eB i
    exact (eFib (eB i) a).property
  have hGraph :
      G.comap φ = EPPAIII.cliqueUnion (Fintype.card B) t := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change G.Adj (φ x) (φ y) ↔
      (x.1 = y.1 ∧ x.2 ≠ y.2)
    rw [hAdj (φ x) (φ y)]
    have hSame : (f (φ x) = f (φ y)) ↔
        x.1 = y.1 := by
      rw [hMap x,hMap y]
      constructor
      · exact eB.injective
      · exact congrArg eB
    have hDifferent : (φ x ≠ φ y) ↔ x ≠ y := by
      constructor
      · intro h heq
        exact h (congrArg φ heq)
      · intro h heq
        exact h (φ.injective heq)
    rw [hSame,hDifferent]
    constructor
    · rintro ⟨hi,hxy⟩
      refine ⟨hi,?_⟩
      intro ha
      exact hxy (Prod.ext hi ha)
    · rintro ⟨hi,ha⟩
      refine ⟨hi,?_⟩
      intro hxy
      exact ha (congrArg Prod.snd hxy)
  have hModel : EPPAIII.DoubleCover.IsHomogeneousGraph (G.comap φ) := by
    rw [hGraph]
    exact EPPAIII.CliqueCovers.cliqueUnion_isHomogeneous _ _
  have hBack :=
    homogeneous_comap_equiv (G.comap φ) φ.symm hModel
  have hBackGraph : (G.comap φ).comap φ.symm = G := by
    apply SimpleGraph.ext
    funext x y
    apply propext
    change G.Adj (φ (φ.symm x)) (φ (φ.symm y)) ↔ G.Adj x y
    simp
  simpa only [hBackGraph] using hBack

end EPPAIII.TwoGraphs
