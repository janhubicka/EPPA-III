import EPPAIII.BlockSystems.CycleFiveMatchingModels
import EPPAIII.BlockSystems.TransitivePartition

/-!
# A short computational certificate of Petersen primitivity

The Petersen matching model has ten vertices. A single explicit
automorphism fixes root (false,0) and acts on the remaining nine
vertices in two cycles, of lengths three and six. Consequently
an invariant block containing the root has order 1,4,7 or 10;
in particular it cannot have order two or five.

In a transitive action on ten vertices, every nontrivial invariant
partition has blocks of size two or five. The two constraints
are incompatible. This uses one certified automorphism, rather
than enumerating all 120 automorphisms or any subgroup machinery.

We intentionally state transitivity of the matching model as a
hypothesis: it will be transported from the *actual* host by its
canonical graph equivalence. Thus we do not need to prove a
separate transitivity theorem about the Petersen graph.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 16384
set_option maxHeartbeats 0

/-- Explicit ten-vertex numbering (bottom 0--4, top 5--9). -/
def petersenVertexIndex (v : Bool × Fin 5) : Fin 10 :=
  ⟨(if v.1 then 5 else 0) + v.2.val, by
    have hv := v.2.isLt
    cases v.1 <;> simp_all <;> omega⟩

def petersenVertexFromIndex (i : Fin 10) : Bool × Fin 5 :=
  (decide (5 ≤ i.val), ⟨i.val % 5, by omega⟩)

def petersenVertexEquiv : (Bool × Fin 5) ≃ Fin 10 where
  toFun := petersenVertexIndex
  invFun := petersenVertexFromIndex
  left_inv := by decide
  right_inv := by decide

/-- A root-fixing Petersen automorphism:
0 fixed, cycles (1 4 5) and (2 3 8 6 9 7). -/
def petersenIndexMove (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 0
  | 1 => 4
  | 2 => 3
  | 3 => 8
  | 4 => 5
  | 5 => 1
  | 6 => 9
  | 7 => 2
  | 8 => 6
  | _ => 7

def petersenIndexUnmove (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 0
  | 1 => 5
  | 2 => 7
  | 3 => 2
  | 4 => 1
  | 5 => 4
  | 6 => 8
  | 7 => 9
  | 8 => 3
  | _ => 6

def petersenIndexAut : Equiv.Perm (Fin 10) where
  toFun := petersenIndexMove
  invFun := petersenIndexUnmove
  left_inv := by decide
  right_inv := by decide

def petersenRootAut : Equiv.Perm (Bool × Fin 5) :=
  (petersenVertexEquiv.trans petersenIndexAut).trans
    petersenVertexEquiv.symm

theorem petersenRootAut_fixes_root :
    petersenRootAut (false,0) = (false,0) := by
  decide

/-- Check every pair of vertices: the explicit permutation
really is an automorphism of the Petersen matching model. -/
theorem petersenRootAut_graph_automorphism :
    IsGraphAutomorphism (cycleFiveMatchingGraph true)
      petersenRootAut := by
  change ∀ u v : Bool × Fin 5,
    (cycleFiveMatchingGraph true).Adj u v ↔
    (cycleFiveMatchingGraph true).Adj
      (petersenRootAut u) (petersenRootAut v)
  decide

/-- Exhaustive finite certificate on just the 1024 vertex subsets:
a root-containing set invariant under the single root-fixing
automorphism can have neither two nor five elements. -/
theorem petersenRootAut_no_two_or_five_invariant_set :
    ∀ S : Finset (Bool × Fin 5),
      (false,0) ∈ S →
      (∀ v : Bool × Fin 5,
        (v ∈ S ↔ petersenRootAut v ∈ S)) →
      S.card ≠ 2 ∧ S.card ≠ 5 := by
  decide

/-- A block for the full automorphism group is in particular
invariant under this root-fixing automorphism if it contains
the root. Hence its size cannot be two or five. -/
theorem petersen_root_block_not_two_or_five
    {B : Type*} [DecidableEq B]
    (block : Bool × Fin 5 → B)
    (hInv : InvariantBlockMap (cycleFiveMatchingGraph true) block) :
    let S : Finset (Bool × Fin 5) :=
      (Finset.univ : Finset (Bool × Fin 5)).filter
        (fun v => block v = block (false,0))
    S.card ≠ 2 ∧ S.card ≠ 5 := by
  classical
  let S : Finset (Bool × Fin 5) :=
    (Finset.univ : Finset (Bool × Fin 5)).filter
      (fun v => block v = block (false,0))
  have hRoot : (false,0) ∈ S := by simp [S]
  have hStable : ∀ v : Bool × Fin 5,
      v ∈ S ↔ petersenRootAut v ∈ S := by
    intro v
    have h := hInv petersenRootAut
      petersenRootAut_graph_automorphism (false,0) v
    rw [petersenRootAut_fixes_root] at h
    simpa only [S, Finset.mem_filter, Finset.mem_univ,
      true_and, eq_comm] using h
  exact petersenRootAut_no_two_or_five_invariant_set S
    hRoot hStable

/-- A nontrivial invariant partition of a ten-vertex transitive
graph must have 2 or 5 vertices in each block. Both are impossible
for the Petersen matching model, by the preceding one-automorphism
certificate. -/
theorem petersen_no_nontrivial_invariant_partition
    {B : Type*} [Fintype B] [DecidableEq B]
    (block : Bool × Fin 5 → B)
    (hInv : InvariantBlockMap (cycleFiveMatchingGraph true) block)
    (hSurj : Function.Surjective block)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms
      (cycleFiveMatchingGraph true))
    (hManyBlocks : 2 ≤ Fintype.card B)
    (hNontrivial : ∃ b : B,
      2 ≤ ((Finset.univ : Finset (Bool × Fin 5)).filter
        (fun v => block v = b)).card) : False := by
  classical
  let S : Finset (Bool × Fin 5) :=
    (Finset.univ : Finset (Bool × Fin 5)).filter
      (fun v => block v = block (false,0))
  let m : ℕ := S.card
  have hUniform : ∀ b : B,
      ((Finset.univ : Finset (Bool × Fin 5)).filter
        (fun v => block v = b)).card = m := by
    intro b
    exact transitive_block_fibres_equal
      (cycleFiveMatchingGraph true) block hTrans
      hInv hSurj b (block (false,0))
  have hCard : Fintype.card B * m = 10 := by
    have h :=
      uniform_partition_card_formula block m hUniform
    simpa using h
  obtain ⟨b,hb⟩ := hNontrivial
  have hMin : 2 ≤ m := by
    calc
      2 ≤ ((Finset.univ : Finset (Bool × Fin 5)).filter
          (fun v => block v = b)).card := hb
      _ = m := hUniform b
  have hMax : m ≤ 5 := by
    have hMul : 2 * m ≤ Fintype.card B * m :=
      Nat.mul_le_mul_right m hManyBlocks
    omega
  have hCases : m = 2 ∨ m = 5 := by
    interval_cases m <;> omega
  have hNo := petersen_root_block_not_two_or_five block hInv
  change m ≠ 2 ∧ m ≠ 5 at hNo
  rcases hCases with hTwo | hFive
  · exact hNo.1 hTwo
  · exact hNo.2 hFive

end EPPAIII.BlockSystems
