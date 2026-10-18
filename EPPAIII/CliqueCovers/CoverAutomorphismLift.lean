import EPPAIII.EPPA.Definitions
import EPPAIII.DoubleCover.RigidLayerHomogeneity

/-!
# Automorphism lifting for generalized clique covers

Every automorphism of the distinguished union of equal cliques extends
diagonally to every uniform generalized clique cover. The argument does
not require a coherent choice of EPPA extensions or a lower bound on
the clique parameters.

The final theorem makes the sufficiency of the uniform covers explicit,
conditional only on homogeneity of the distinguished clique union.
That latter, classical finite cluster-graph fact is kept as a separate
formalization obligation.
-/

namespace EPPAIII.CliqueCovers

/-- Being in the same selected clique means equality or adjacency. -/
private theorem clique_index_eq_iff_eq_or_adj {s t : ℕ}
    (x y : Fin s × Fin t) :
    x.1 = y.1 ↔ x = y ∨ (cliqueUnion s t).Adj x y := by
  change x.1 = y.1 ↔ x = y ∨ (x.1 = y.1 ∧ x.2 ≠ y.2)
  constructor
  · intro h
    by_cases hxy : x = y
    · exact Or.inl hxy
    · right
      refine ⟨h, ?_⟩
      intro ha
      exact hxy (Prod.ext h ha)
  · rintro (h | h)
    · exact congrArg Prod.fst h
    · exact h.1

/-- Every base automorphism preserves the unordered clique partition,
including the degenerate singleton-clique case. -/
theorem base_aut_preserves_clique_index {s t : ℕ}
    (p : Equiv.Perm (Fin s × Fin t))
    (hp : IsGraphAutomorphism (cliqueUnion s t) p)
    (x y : Fin s × Fin t) :
    x.1 = y.1 ↔ (p x).1 = (p y).1 := by
  calc
    x.1 = y.1 ↔
        x = y ∨ (cliqueUnion s t).Adj x y :=
      clique_index_eq_iff_eq_or_adj x y
    _ ↔ p x = p y ∨
        (cliqueUnion s t).Adj (p x) (p y) := by
      constructor
      · rintro (h | h)
        · exact Or.inl (congrArg p h)
        · exact Or.inr ((hp x y).mp h)
      · rintro (h | h)
        · exact Or.inl (p.injective h)
        · exact Or.inr ((hp x y).mpr h)
    _ ↔ (p x).1 = (p y).1 :=
      (clique_index_eq_iff_eq_or_adj (p x) (p y)).symm

/-- Use the same base permutation on both halves of the cover. -/
def coverLiftBase {s t : ℕ}
    (p : Equiv.Perm (Fin s × Fin t)) :
    Equiv.Perm (CoverVertex s t) where
  toFun := fun u => (u.1, p u.2)
  invFun := fun u => (u.1, p.symm u.2)
  left_inv := by
    intro u
    rcases u with ⟨side, x⟩
    simp
  right_inv := by
    intro u
    rcases u with ⟨side, x⟩
    simp

/-- On a fixed clique, each of the four diagonal relation types
is invariant under arbitrary base automorphisms. -/
private theorem base_aut_preserves_diagonal_type {s t : ℕ}
    (X : CrossType)
    (p : Equiv.Perm (Fin s × Fin t))
    (hp : IsGraphAutomorphism (cliqueUnion s t) p)
    (x y : Fin s × Fin t) (hIndex : x.1 = y.1) :
    X.rel x.2 y.2 ↔ X.rel (p x).2 (p y).2 := by
  have hIndex' : (p x).1 = (p y).1 :=
    (base_aut_preserves_clique_index p hp x y).mp hIndex
  have hCoord : x.2 = y.2 ↔ (p x).2 = (p y).2 := by
    constructor
    · intro h
      have hXY : x = y := Prod.ext hIndex h
      exact congrArg Prod.snd (congrArg p hXY)
    · intro h
      have hPXY : p x = p y := Prod.ext hIndex' h
      exact congrArg Prod.snd (p.injective hPXY)
  cases X <;> simp [CrossType.rel, hCoord]

/-- Any automorphism of the base graph extends to an automorphism of
every uniform generalized clique cover and fixes the side coordinate. -/
theorem coverLiftBase_graphAut {s t : ℕ}
    (X : CrossType) (Y : Bool)
    (p : Equiv.Perm (Fin s × Fin t))
    (hp : IsGraphAutomorphism (cliqueUnion s t) p) :
    IsGraphAutomorphism (coverGraph s t X Y) (coverLiftBase p) := by
  intro u v
  rcases u with ⟨sideU,x⟩
  rcases v with ⟨sideV,y⟩
  change coverAdj X Y (sideU,x) (sideV,y) ↔
    coverAdj X Y (sideU,p x) (sideV,p y)
  by_cases hSide : sideU = sideV
  · have hBase := hp x y
    change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔
      ((p x).1 = (p y).1 ∧ (p x).2 ≠ (p y).2) at hBase
    simpa [coverAdj,hSide] using hBase
  · have hIndex := base_aut_preserves_clique_index p hp x y
    have hCross :
        (if x.1 = y.1 then X.rel x.2 y.2 else Y = true) ↔
        (if (p x).1 = (p y).1 then
           X.rel (p x).2 (p y).2 else Y = true) := by
      by_cases hXY : x.1 = y.1
      · have hPXY := hIndex.mp hXY
        simpa [hXY,hPXY] using
          (base_aut_preserves_diagonal_type X p hp x y hXY)
      · have hPXY : (p x).1 ≠ (p y).1 :=
          fun h => hXY (hIndex.mpr h)
        simp [hXY,hPXY]
    simpa [coverAdj,hSide] using hCross

/-- Any uniform generalized clique cover is an EPPA witness for its
selected clique union, provided the latter is homogeneous.
This separates the genuinely graph-theoretic lifting argument
from the elementary classification of homogeneous cluster graphs. -/
theorem uniform_cover_eppa_of_base_homogeneous {s t : ℕ}
    (X : CrossType) (Y : Bool)
    (hHom : DoubleCover.IsHomogeneousGraph (cliqueUnion s t)) :
    CoverIsEPPA s t X Y := by
  refine ⟨coverLeftEmbedding_induced s t X Y, ?_⟩
  intro D p hp
  obtain ⟨q,hq,hExtend⟩ := hHom D p hp
  refine ⟨coverLiftBase q, coverLiftBase_graphAut X Y q hq, ?_⟩
  intro v hv
  change (false, q v) = (false, p v)
  exact congrArg (fun x => (false, x)) (hExtend v hv)

end EPPAIII.CliqueCovers
