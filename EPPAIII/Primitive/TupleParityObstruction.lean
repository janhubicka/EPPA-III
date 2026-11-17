import EPPAIII.EPPA.ComplementTransport

/-!
# A finite EPPA obstruction from parity of non-neighbors

For a tuple, count the entries distinct from and nonadjacent to a test
vertex. Constancy of this count modulo two over the whole host is preserved
by every host automorphism. Opposite constancy values certify an obstruction
to extending a partial isomorphism between the two tuples.
-/

namespace EPPAIII.Primitive

open scoped BigOperators

variable {V W I : Type*} [Fintype I]

/-- The parity at a test vertex of the number of tuple entries joined to it
in the complementary graph. -/
def tupleParity (H : SimpleGraph W) [DecidableEq W] [DecidableRel H.Adj]
    (points : I → W) (test : W) : Nat :=
  (∑ i, if Hᶜ.Adj (points i) test then 1 else 0) % 2

/-- A tuple has constant parity if every vertex sees the same parity. -/
def TupleParityConstant (H : SimpleGraph W) [DecidableEq W] [DecidableRel H.Adj]
    (points : I → W) : Prop :=
  ∀ x y, tupleParity H points x = tupleParity H points y

theorem tupleParity_map (H : SimpleGraph W) [DecidableEq W] [DecidableRel H.Adj]
    (points : I → W) (test : W) (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    tupleParity H (q ∘ points) (q test) = tupleParity H points test := by
  unfold tupleParity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (if Hᶜ.Adj (q (points i)) (q test) then 1 else 0) =
    (if Hᶜ.Adj (points i) test then 1 else 0)
  have hAdj := BlockSystems.graphAutomorphism_complement H q hq (points i) test
  by_cases h : Hᶜ.Adj (points i) test
  · simp only [ite_eq_left h, ite_eq_left (hAdj.mp h)]
  · simp only [ite_eq_right h, ite_eq_right (fun h' => h (hAdj.mpr h'))]

theorem tupleParityConstant_map_iff (H : SimpleGraph W)
    [DecidableEq W] [DecidableRel H.Adj]
    (points : I → W) (q : Equiv.Perm W) (hq : IsGraphAutomorphism H q) :
    TupleParityConstant H (q ∘ points) ↔ TupleParityConstant H points := by
  constructor
  · intro h x y
    simpa only [tupleParity_map H points _ q hq] using h (q x) (q y)
  · intro h x y
    obtain ⟨a, rfl⟩ := q.surjective x
    obtain ⟨b, rfl⟩ := q.surjective y
    simpa only [tupleParity_map H points _ q hq] using h a b

/-- A partial automorphism whose domain covers the selected tuple must
preserve parity constancy as evaluated across the host. -/
theorem tupleParityConstant_of_eppa (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableEq W] [DecidableRel H.Adj]
    (e : V ↪ W) (he : IsEPPAEmbedding G H e) (points : I → V)
    (domain : Finset V) (p : Equiv.Perm V) (hp : IsPartialGraphAutomorphism G domain p)
    (hDomain : ∀ i, points i ∈ domain) :
    TupleParityConstant H (e ∘ p ∘ points) ↔ TupleParityConstant H (e ∘ points) := by
  obtain ⟨q, hq, hExtend⟩ := he.2 domain p hp
  have hMap : e ∘ p ∘ points = q ∘ e ∘ points := by
    funext i
    exact (hExtend (points i) (hDomain i)).symm
  rw [hMap]
  exact tupleParityConstant_map_iff H (e ∘ points) q hq

end EPPAIII.Primitive
