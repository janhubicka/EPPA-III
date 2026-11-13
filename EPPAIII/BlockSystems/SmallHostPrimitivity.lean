import EPPAIII.BlockSystems.SmallHostOrbitalGraph
import EPPAIII.BlockSystems.ClosedConnectedComponents

/-!
# Primitive actions and invariant bipartite orbital graphs

Primitivity of the actual host automorphism action is expressed as the
absence of nontrivial invariant equivalence relations. A nonempty
invariant orbital graph must then be connected, since otherwise the
reachability relation would be a nontrivial invariant equivalence.

If all orbital edges cross a given Bool bipartition, connectedness
forces every automorphism to preserve the bipartition (up to swapping
the sides). Thus the bipartition is a nontrivial block system unless
each side has only one vertex.

This module is independent of EPPA. It will be used for the equality
case of the small-host rank-three proposition.
-/

namespace EPPAIII.BlockSystems

/-- The full automorphism group of H is primitive precisely when
every invariant equivalence relation is equality or universal.
This is the standard block-system definition of primitivity. -/
def IsPrimitiveAutAction {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ (R : W → W → Prop), Equivalence R →
    (∀ (q : Equiv.Perm W), IsGraphAutomorphism H q →
      ∀ u v : W, R u v ↔ R (q u) (q v)) →
    (∀ u v : W, R u v → u = v) ∨
      (∀ u v : W, R u v)

/-- A primitive group cannot preserve a disconnected graph having
at least one edge. This uses reachability as an invariant equivalence
relation; transitivity and EPPA are not needed. -/
theorem primitive_invariant_nonempty_graph_preconnected {W : Type*}
    (H F : SimpleGraph W)
    (hPrim : IsPrimitiveAutAction H)
    (hInvariant : ∀ (q : Equiv.Perm W),
      IsGraphAutomorphism H q → IsGraphAutomorphism F q)
    (a b : W) (hab : F.Adj a b) :
    F.Preconnected := by
  have hInvReach :
      ∀ (q : Equiv.Perm W), IsGraphAutomorphism H q →
        ∀ u v : W, F.Reachable u v ↔
          F.Reachable (q u) (q v) := by
    intro q hq u v
    exact (graphAutomorphism_reachable_iff F q
      (hInvariant q hq) u v).symm
  rcases hPrim F.Reachable F.reachable_is_equivalence hInvReach with
    hDiscrete | hUniversal
  · have hReach : F.Reachable a b := hab.reachable
    exact False.elim ((F.ne_of_adj hab) (hDiscrete a b hReach))
  · exact hUniversal

/-- Flipping both Boolean coordinates preserves their XOR. -/
private theorem bool_xor_of_opposite_bits
    (a b c d : Bool) (hab : a ≠ b) (hcd : c ≠ d) :
    Bool.xor a c = Bool.xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Bool.xor]

/-- Equal XOR discrepancy forces equality-status preservation. -/
private theorem bool_eq_iff_of_xor_eq
    (a b c d : Bool)
    (h : Bool.xor a c = Bool.xor b d) :
    (a = b ↔ c = d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [Bool.xor]

/-- A connected bipartite graph on Bool × V has an intrinsic
bipartition: automorphisms preserve the sides up to their interchange.
The proof propagates the Boolean side discrepancy along graph walks. -/
theorem connected_bipartite_automorphism_preserves_side_relation
    {V : Type*}
    (F : SimpleGraph (Bool × V))
    (hConn : F.Preconnected)
    (hCross : ∀ u v : Bool × V,
      F.Adj u v → u.1 ≠ v.1)
    (q : Equiv.Perm (Bool × V))
    (hq : IsGraphAutomorphism F q) :
    ∀ u v : Bool × V, (u.1 = v.1 ↔ (q u).1 = (q v).1) := by
  intro u v
  let P : Bool × V → Prop :=
    fun z => Bool.xor z.1 (q z).1 = Bool.xor u.1 (q u).1
  have hClosed :
      ∀ z ∈ (Set.setOf P), ∀ w : Bool × V,
        F.Adj z w → w ∈ (Set.setOf P) := by
    intro z hz w hzw
    change P z at hz
    change P w
    have hFlip :=
      bool_xor_of_opposite_bits
        z.1 w.1 (q z).1 (q w).1
        (hCross z w hzw)
        (hCross (q z) (q w) ((hq z w).mp hzw))
    exact hFlip.symm.trans hz
  have hAtU : u ∈ (Set.setOf P) := by
    rfl
  have hAtV : v ∈ (Set.setOf P) :=
    reachable_mem_of_adj_closed F (Set.setOf P)
      hClosed u v hAtU (hConn u v)
  change Bool.xor v.1 (q v).1 =
      Bool.xor u.1 (q u).1 at hAtV
  exact bool_eq_iff_of_xor_eq
    u.1 v.1 (q u).1 (q v).1 hAtV.symm

/-- A nonempty invariant cross-side graph in a primitive action
forces the common half-vertex type to be subsingleton. -/
theorem primitive_invariant_cross_graph_subsingleton
    {V : Type*} (H F : SimpleGraph (Bool × V))
    (hPrim : IsPrimitiveAutAction H)
    (hInvariant : ∀ (q : Equiv.Perm (Bool × V)),
      IsGraphAutomorphism H q → IsGraphAutomorphism F q)
    (hCross : ∀ u v : Bool × V, F.Adj u v → u.1 ≠ v.1)
    (a b : Bool × V) (hab : F.Adj a b) :
    Subsingleton V := by
  have hConn : F.Preconnected :=
    primitive_invariant_nonempty_graph_preconnected
      H F hPrim hInvariant a b hab
  have hSide :
      ∀ (q : Equiv.Perm (Bool × V)),
        IsGraphAutomorphism H q →
        ∀ u v : Bool × V,
          (u.1 = v.1 ↔ (q u).1 = (q v).1) := by
    intro q hq
    exact connected_bipartite_automorphism_preserves_side_relation
      F hConn hCross q (hInvariant q hq)
  have hEquiv : Equivalence
      (fun u v : Bool × V => u.1 = v.1) := by
    constructor
    · intro u
      rfl
    · intro u v h
      exact h.symm
    · intro u v w h h'
      exact h.trans h'
  rcases hPrim (fun u v : Bool × V => u.1 = v.1)
      hEquiv hSide with hDiscrete | hUniversal
  · refine ⟨?_⟩
    intro x y
    exact congrArg Prod.snd
      (hDiscrete (false,x) (false,y) rfl)
  · have hBad := hUniversal (false,a.2) (true,a.2)
    exact False.elim (Bool.false_ne_true hBad)

/-- The contradiction in its most useful form: if a half has two
different vertices, a primitive host cannot have a nonempty invariant
graph all of whose edges cross the balanced cut. -/
theorem primitive_forbids_nonempty_invariant_cross_graph
    {V : Type*} (H F : SimpleGraph (Bool × V))
    (hPrim : IsPrimitiveAutAction H)
    (hInvariant : ∀ (q : Equiv.Perm (Bool × V)),
      IsGraphAutomorphism H q → IsGraphAutomorphism F q)
    (hCross : ∀ u v : Bool × V, F.Adj u v → u.1 ≠ v.1)
    (x y : V) (hxy : x ≠ y)
    (a b : Bool × V) (hab : F.Adj a b) :
    False := by
  have hSub : Subsingleton V :=
    primitive_invariant_cross_graph_subsingleton
      H F hPrim hInvariant hCross a b hab
  exact hxy (hSub.elim x y)

end EPPAIII.BlockSystems
