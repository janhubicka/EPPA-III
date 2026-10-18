import EPPAIII.CliqueCovers.CoverVertexTransitivity
import EPPAIII.CliqueCovers.WagnerHostConclusion

/-!
# Exceptional Wagner graph: EPPA and vertex transitivity

The selected first half of the canonical Wagner graph is an induced
2K2. Three explicit automorphisms lift the independent flips of
the two selected K2s and their interchange. Eight products represent
all eight base automorphisms. An additional involution interchanges
the two halves and makes the full Wagner graph vertex-transitive.

All finite claims are decided over at most 24 base permutations,
8 lifting candidates, and 16 host automorphisms. We do *not* search
over all 8! host permutations and make no nonstandard axiom.
-/

namespace EPPAIII.CliqueCovers

set_option maxRecDepth 8192
set_option maxHeartbeats 0

private def bitFlip (a : Fin 2) : Fin 2 := a + 1

/-- Lift the independent transposition of the first selected K2. -/
private def wagnerFlipFirstFn (u : CoverVertex 2 2) : CoverVertex 2 2 :=
  if u.1 then
    (true,(bitFlip u.2.1,u.2.2))
  else
    (false,(u.2.1,if u.2.1 = (0 : Fin 2) then bitFlip u.2.2 else u.2.2))

private def wagnerFlipFirst : Equiv.Perm (CoverVertex 2 2) where
  toFun := wagnerFlipFirstFn
  invFun := wagnerFlipFirstFn
  left_inv := by decide
  right_inv := by decide

/-- Lift the independent transposition of the second selected K2. -/
private def wagnerFlipSecondFn (u : CoverVertex 2 2) : CoverVertex 2 2 :=
  if u.1 then
    (true,(u.2.1,bitFlip u.2.2))
  else
    (false,(u.2.1,if u.2.1 = (1 : Fin 2) then bitFlip u.2.2 else u.2.2))

private def wagnerFlipSecond : Equiv.Perm (CoverVertex 2 2) where
  toFun := wagnerFlipSecondFn
  invFun := wagnerFlipSecondFn
  left_inv := by decide
  right_inv := by decide

/-- Lift interchange of the two selected K2 components. -/
private def wagnerSwapCliquesFn (u : CoverVertex 2 2) : CoverVertex 2 2 :=
  if u.1 then
    (true,(u.2.2,u.2.1))
  else
    (false,(bitFlip u.2.1,u.2.2))

private def wagnerSwapCliques : Equiv.Perm (CoverVertex 2 2) where
  toFun := wagnerSwapCliquesFn
  invFun := wagnerSwapCliquesFn
  left_inv := by decide
  right_inv := by decide

/-- Eight explicit graph automorphisms realizing the full selected
S2 wr S2 action. -/
private def wagnerBaseChoice (i : Fin 8) :
    Equiv.Perm (CoverVertex 2 2) :=
  if i = 0 then Equiv.refl _
  else if i = 1 then wagnerFlipFirst
  else if i = 2 then wagnerFlipSecond
  else if i = 3 then wagnerSwapCliques
  else if i = 4 then wagnerFlipFirst.trans wagnerFlipSecond
  else if i = 5 then wagnerFlipFirst.trans wagnerSwapCliques
  else if i = 6 then wagnerFlipSecond.trans wagnerSwapCliques
  else (wagnerFlipFirst.trans wagnerFlipSecond).trans wagnerSwapCliques

private theorem wagnerBaseChoice_aut (i : Fin 8) :
    IsGraphAutomorphism wagnerCanonicalGraph (wagnerBaseChoice i) := by
  fin_cases i <;> decide

/-- Every graph automorphism of the selected 2K2 is the restriction
of one of our eight explicitly verified host automorphisms. -/
private theorem wagnerBaseChoice_extends :
    ∀ (p : Equiv.Perm (Fin 2 × Fin 2)),
      IsGraphAutomorphism (cliqueUnion 2 2) p →
      ∃ i : Fin 8,
        ∀ x : Fin 2 × Fin 2,
          wagnerBaseChoice i (false,x) = (false,p x) := by
  decide

/-- An involution interchanging the halves of the Wagner graph.
On the selected half it maps (i,a) to the outside corner (a,i+a);
the inverse takes corner (j,k) back to selected (j+k,j). -/
private def wagnerExchangeFn (u : CoverVertex 2 2) : CoverVertex 2 2 :=
  if u.1 then
    (false,(u.2.1+u.2.2,u.2.1))
  else
    (true,(u.2.2,u.2.1+u.2.2))

private def wagnerExchange : Equiv.Perm (CoverVertex 2 2) where
  toFun := wagnerExchangeFn
  invFun := wagnerExchangeFn
  left_inv := by decide
  right_inv := by decide

private theorem wagnerExchange_aut :
    IsGraphAutomorphism wagnerCanonicalGraph wagnerExchange := by
  decide

private def wagnerTransitiveChoice (c : Bool × Fin 8) :
    Equiv.Perm (CoverVertex 2 2) :=
  if c.1 then (wagnerBaseChoice c.2).trans wagnerExchange
  else wagnerBaseChoice c.2

private theorem wagnerTransitiveChoice_aut (c : Bool × Fin 8) :
    IsGraphAutomorphism wagnerCanonicalGraph
      (wagnerTransitiveChoice c) := by
  rcases c with ⟨b,i⟩
  cases b with
  | false => exact wagnerBaseChoice_aut i
  | true =>
    intro x y
    exact (wagnerBaseChoice_aut i x y).trans
      (wagnerExchange_aut _ _)

/-- Every pair of vertices can be joined by one of the sixteen
explicitly verified Wagner graph automorphisms. -/
private theorem wagnerChoices_transitive :
    ∀ u v : CoverVertex 2 2,
      ∃ c : Bool × Fin 8, wagnerTransitiveChoice c u = v := by
  decide

/-- The exceptional Wagner graph is vertex-transitive. -/
theorem wagnerCanonical_vertexTransitive :
    HasTransitiveGraphAutomorphisms wagnerCanonicalGraph := by
  intro u v
  obtain ⟨c,hc⟩ := wagnerChoices_transitive u v
  exact ⟨wagnerTransitiveChoice c,wagnerTransitiveChoice_aut c,hc⟩

private theorem wagnerCanonical_left_induced :
    IsInducedGraphEmbedding (cliqueUnion 2 2)
      wagnerCanonicalGraph (coverLeftEmbedding 2 2) := by
  decide

/-- The Wagner graph is an actual EPPA witness for its designated
induced 2K2, not merely a possible result of a classification. -/
theorem wagnerCanonical_isEPPA :
    IsEPPAEmbedding (cliqueUnion 2 2) wagnerCanonicalGraph
      (coverLeftEmbedding 2 2) := by
  constructor
  · exact wagnerCanonical_left_induced
  · intro D p hp
    obtain ⟨sigma,hsigma,hAgree⟩ :=
      cliqueUnion_isHomogeneous 2 2 D p hp
    obtain ⟨i,hLift⟩ := wagnerBaseChoice_extends sigma hsigma
    refine ⟨wagnerBaseChoice i,wagnerBaseChoice_aut i,?_⟩
    intro x hx
    change wagnerBaseChoice i (false,x) = (false,p x)
    calc
      wagnerBaseChoice i (false,x) = (false,sigma x) := hLift x
      _ = (false,p x) := congrArg (fun z => (false,z)) (hAgree x hx)

end EPPAIII.CliqueCovers
