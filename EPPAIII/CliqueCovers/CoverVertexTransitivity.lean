import EPPAIII.CliqueCovers.CoverAutomorphismLift
import EPPAIII.CliqueCovers.TransitiveHalfEdges

/-!
# Vertex transitivity of every uniform generalized clique cover

A simultaneous permutation of clique indices and of within-clique
coordinates moves any chosen base vertex to another. The already
verified diagonal cover lift moves both sides in the same way. The
canonical side flip interchanges the two halves.

Thus all uniform generalized clique-cover graphs are vertex-transitive,
including the degenerate cases. Together with
`uniform_cover_isEPPA` this certifies the constructive/sufficiency
direction of the generalized-cover class in the manuscript.
-/

namespace EPPAIII.CliqueCovers

/-- The disjoint union of equal cliques has a transitive automorphism
group; the required permutations are just coordinate swaps. -/
theorem cliqueUnion_transitive_via_swaps (s t : ℕ) :
    HasTransitiveGraphAutomorphisms (cliqueUnion s t) := by
  intro u v
  let pi : Equiv.Perm (Fin s) := Equiv.swap u.1 v.1
  let rho : Equiv.Perm (Fin t) := Equiv.swap u.2 v.2
  let p : Equiv.Perm (Fin s × Fin t) := Equiv.prodCongr pi rho
  refine ⟨p, ?_, ?_⟩
  · intro x y
    change (x.1 = y.1 ∧ x.2 ≠ y.2) ↔
      (pi x.1 = pi y.1 ∧ rho x.2 ≠ rho y.2)
    constructor
    · rintro ⟨hi, ha⟩
      exact ⟨congrArg pi hi, rho.injective.ne ha⟩
    · rintro ⟨hi, ha⟩
      exact ⟨pi.injective hi, fun hab => ha (congrArg rho hab)⟩
  · apply Prod.ext
    · change pi u.1 = v.1
      simp [pi]
    · change rho u.2 = v.2
      simp [rho]

/-- The canonical involution exchanging the two halves of a cover. -/
def coverSideSwap {s t : ℕ} : Equiv.Perm (CoverVertex s t) where
  toFun := fun u => (!u.1,u.2)
  invFun := fun u => (!u.1,u.2)
  left_inv := by
    intro u
    rcases u with ⟨b,x⟩
    cases b <;> rfl
  right_inv := by
    intro u
    rcases u with ⟨b,x⟩
    cases b <;> rfl

/-- Uniform cover cross-relations are symmetric between the two halves. -/
theorem coverSideSwap_graphAut {s t : ℕ}
    (X : CrossType) (Y : Bool) :
    IsGraphAutomorphism (coverGraph s t X Y)
      (coverSideSwap (s := s) (t := t)) := by
  intro u v
  rcases u with ⟨bu,x⟩
  rcases v with ⟨bv,y⟩
  cases bu <;> cases bv <;>
    simp [coverSideSwap,coverGraph,coverAdj]

/-- Every uniform generalized clique cover is a vertex-transitive
graph, independently of its diagonal and off-diagonal relation types. -/
theorem uniform_cover_vertex_transitive (s t : ℕ)
    (X : CrossType) (Y : Bool) :
    HasTransitiveGraphAutomorphisms (coverGraph s t X Y) := by
  intro u v
  obtain ⟨p,hp,hpMap⟩ :=
    cliqueUnion_transitive_via_swaps s t u.2 v.2
  let q : Equiv.Perm (CoverVertex s t) := coverLiftBase p
  have hq : IsGraphAutomorphism (coverGraph s t X Y) q :=
    coverLiftBase_graphAut X Y p hp
  by_cases hs : u.1 = v.1
  · refine ⟨q,hq,?_⟩
    change (u.1,p u.2) = v
    exact Prod.ext hs hpMap
  · let f : Equiv.Perm (CoverVertex s t) := coverSideSwap
    let r : Equiv.Perm (CoverVertex s t) := q.trans f
    have hf : IsGraphAutomorphism (coverGraph s t X Y) f :=
      coverSideSwap_graphAut X Y
    have hr : IsGraphAutomorphism (coverGraph s t X Y) r := by
      intro a b
      change (coverGraph s t X Y).Adj a b ↔
        (coverGraph s t X Y).Adj (f (q a)) (f (q b))
      exact (hq a b).trans (hf (q a) (q b))
    refine ⟨r,hr,?_⟩
    change (!u.1,p u.2) = v
    have hFlip : !u.1 = v.1 := by
      cases hu : u.1 <;> cases hv : v.1 <;>
        simp [hu, hv] at hs ⊢
    exact Prod.ext hFlip hpMap

end EPPAIII.CliqueCovers
