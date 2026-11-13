import EPPAIII.BlockSystems.SmallHostPairOrbits

/-!
# The orbital graph of a host automorphism group

An orbit of an unordered pair of distinct host vertices is a genuine
simple graph. Every automorphism of the original host is an
automorphism of this orbital graph. In particular, transitivity
passes from the host to the orbital graph. This is an independent
module toward the small-host rank-three reduction; no primitivity
argument is claimed here.
-/

namespace EPPAIII.BlockSystems

/-- The graph whose edges are the unordered orbit of {a,b} under
actual automorphisms of H. -/
def unorderedPairOrbitGraph {W : Type*}
    (H : SimpleGraph W) (a b : W) (hab : a ≠ b) : SimpleGraph W where
  Adj := fun u v =>
    ∃ p : Equiv.Perm W, IsGraphAutomorphism H p ∧
      ((p a = u ∧ p b = v) ∨ (p a = v ∧ p b = u))
  symm := by
    constructor
    intro u v
    rintro ⟨p,hp,h⟩
    refine ⟨p,hp,?_⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩
  loopless := by
    constructor
    intro u
    rintro ⟨p,_,h⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact hab (p.injective (ha.trans hb.symm))
    · exact hab (p.injective (ha.trans hb.symm))

/-- The orbital graph contains the prescribed base pair. -/
theorem unorderedPairOrbitGraph_base_edge {W : Type*}
    (H : SimpleGraph W) (a b : W) (hab : a ≠ b) :
    (unorderedPairOrbitGraph H a b hab).Adj a b := by
  refine ⟨Equiv.refl W,?_,Or.inl ⟨rfl,rfl⟩⟩
  intro u v
  rfl

/-- All host automorphisms preserve the associated unordered
pair orbit as a graph, in both directions. -/
theorem unorderedPairOrbitGraph_automorphism {W : Type*}
    (H : SimpleGraph W) (a b : W) (hab : a ≠ b)
    (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism (unorderedPairOrbitGraph H a b hab) q := by
  have hqInv : IsGraphAutomorphism H q.symm := by
    intro u v
    simpa using (hq (q.symm u) (q.symm v)).symm
  intro u v
  constructor
  · rintro ⟨p,hp,h⟩
    have hpq : IsGraphAutomorphism H (p.trans q) := by
      intro x y
      exact (hp x y).trans (hq (p x) (p y))
    refine ⟨p.trans q,hpq,?_⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by simpa using congrArg q ha,
                        by simpa using congrArg q hb⟩
    · exact Or.inr ⟨by simpa using congrArg q ha,
                        by simpa using congrArg q hb⟩
  · rintro ⟨p,hp,h⟩
    have hpq : IsGraphAutomorphism H (p.trans q.symm) := by
      intro x y
      exact (hp x y).trans (hqInv (p x) (p y))
    refine ⟨p.trans q.symm,hpq,?_⟩
    rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inl ⟨by simpa using congrArg q.symm ha,
                        by simpa using congrArg q.symm hb⟩
    · exact Or.inr ⟨by simpa using congrArg q.symm ha,
                        by simpa using congrArg q.symm hb⟩

/-- An orbital graph of a transitive graph is vertex-transitive
under the same automorphism group. -/
theorem unorderedPairOrbitGraph_vertex_transitive {W : Type*}
    (H : SimpleGraph W) (a b : W) (hab : a ≠ b)
    (hTrans : EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    EPPAIII.CliqueCovers.HasTransitiveGraphAutomorphisms
      (unorderedPairOrbitGraph H a b hab) := by
  intro u v
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  exact ⟨q,unorderedPairOrbitGraph_automorphism H a b hab q hq,hqu⟩

end EPPAIII.BlockSystems
