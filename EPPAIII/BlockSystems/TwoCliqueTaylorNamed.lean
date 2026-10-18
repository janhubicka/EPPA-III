import EPPAIII.BlockSystems.TwoCliqueSwitching

/-!
# Naming the Taylor double of a two-clique graph

For a Boolean two-clique base, the Taylor inter-fibre adjacency
splits the doubled vertices into two complete graphs, with the
optional matching of corresponding vertices between them.

The result is a uniform Boolean identity, valid for any vertex type.
No graph classification, finite enumeration, or EPPA hypothesis is
needed for this final graph-name identification.
-/

namespace EPPAIII.BlockSystems

/-- Taylor adjacency for a two-clique base, with optional mate edges. -/
def twoCliqueTaylorRel {V : Type*} (c : V → Bool) (mate : Bool)
    (u v : Bool × V) : Prop :=
  u ≠ v ∧
    (if u.1 = v.1 then c u.2 = c v.2
     else (u.2 ≠ v.2 ∧ c u.2 ≠ c v.2) ∨
       (mate = true ∧ u.2 = v.2))

/-- Two complete graphs labelled by layer XOR base-clique colour,
with a perfect matching between them precisely when mate is true. -/
def twoCliqueMatchedRel {V : Type*} (c : V → Bool) (mate : Bool)
    (u v : Bool × V) : Prop :=
  u ≠ v ∧
    (Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∨
     (mate = true ∧ u.2 = v.2))

def twoCliqueMatchedGraph {V : Type*} (c : V → Bool)
    (mate : Bool) : SimpleGraph (Bool × V) where
  Adj := twoCliqueMatchedRel c mate
  symm := by
    constructor
    intro u v h
    change u ≠ v ∧
      (Bool.xor u.1 (c u.2) = Bool.xor v.1 (c v.2) ∨
       (mate = true ∧ u.2 = v.2)) at h
    change v ≠ u ∧
      (Bool.xor v.1 (c v.2) = Bool.xor u.1 (c u.2) ∨
       (mate = true ∧ v.2 = u.2))
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with heq | hmate
    · exact Or.inl heq.symm
    · exact Or.inr ⟨hmate.1, hmate.2.symm⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

/-- The two apparently different descriptions are the same relation,
for arbitrary sizes of the two base cliques. -/
theorem twoCliqueTaylorRel_iff_matched {V : Type*}
    (c : V → Bool) (mate : Bool) (u v : Bool × V) :
    twoCliqueTaylorRel c mate u v ↔
      twoCliqueMatchedRel c mate u v := by
  rcases u with ⟨a,x⟩
  rcases v with ⟨b,y⟩
  by_cases hxy : x = y
  · subst y
    cases a <;> cases b <;> cases hc : c x <;>
      cases mate <;>
      simp [twoCliqueTaylorRel, twoCliqueMatchedRel, Bool.xor, hc]
  · cases a <;> cases b <;>
      cases hc : c x <;> cases hd : c y <;>
      cases mate <;>
      simp [twoCliqueTaylorRel, twoCliqueMatchedRel,
        Bool.xor, hxy, hc, hd]

/-- Any graph with the actual Taylor pair adjacency is exactly
the named pair of complete cliques with its optional matching. -/
theorem twoCliqueTaylorGraph_eq_matched {V : Type*}
    (c : V → Bool) (mate : Bool)
    (H : SimpleGraph (Bool × V))
    (hTaylor : ∀ u v, H.Adj u v ↔
      twoCliqueTaylorRel c mate u v) :
    H = twoCliqueMatchedGraph c mate := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  exact (hTaylor u v).trans
    (twoCliqueTaylorRel_iff_matched c mate u v)

end EPPAIII.BlockSystems
