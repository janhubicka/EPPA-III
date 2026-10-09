import Mathlib

/-!
# Generalised clique covers

A literal graph model of Definitions 1.5--1.6 in the EPPA-III draft.

Vertices are indexed by a side (the original or second copy), a clique
index, and a coordinate within the clique. Internal edges form copies of
the disjoint union of `s` cliques of size `t`. The diagonal cross-block
relation has one of four types; the off-diagonal relation is either empty
or complete.

This file verifies the elementary structural facts. It does NOT assume,
or claim to establish, Lemma 3.7 or Claims 3.8--3.11.
-/

namespace EPPAIII

inductive CrossType where
  | empty
  | full
  | matching
  | coMatching
  deriving DecidableEq, Repr

/-- Connection relation within a diagonal block of the connection matrix. -/
def CrossType.rel {t : Nat} (X : CrossType) (a b : Fin t) : Prop :=
  match X with
  | .empty => False
  | .full => True
  | .matching => a = b
  | .coMatching => a ≠ b

theorem CrossType.rel_comm {t : Nat} (X : CrossType) (a b : Fin t) :
    X.rel a b ↔ X.rel b a := by
  cases X <;> simp [CrossType.rel, eq_comm, ne_comm]

/-- A side, a clique index, and an index inside a clique. -/
abbrev CoverVertex (s t : Nat) := Bool × (Fin s × Fin t)

def left {s t : Nat} (i : Fin s) (a : Fin t) : CoverVertex s t :=
  (false, (i, a))

def right {s t : Nat} (i : Fin s) (a : Fin t) : CoverVertex s t :=
  (true, (i, a))

/-- Edge relation of the uniform generalised clique cover. -/
def coverAdj {s t : Nat} (X : CrossType) (Y : Bool)
    (x y : CoverVertex s t) : Prop :=
  (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 ≠ y.1 ∧
    if x.2.1 = y.2.1 then X.rel x.2.2 y.2.2 else Y = true)

theorem coverAdj_flip {s t : Nat} (X : CrossType) (Y : Bool)
    (x y : CoverVertex s t) :
    coverAdj X Y x y → coverAdj X Y y x := by
  intro h
  rcases h with ⟨hs, hi, ha⟩ | ⟨hs, hc⟩
  · exact Or.inl ⟨hs.symm, hi.symm, ha.symm⟩
  · apply Or.inr
    refine ⟨hs.symm, ?_⟩
    by_cases hi : x.2.1 = y.2.1
    · have hxy : X.rel x.2.2 y.2.2 := by simpa [hi] using hc
      have hyx : X.rel y.2.2 x.2.2 :=
        (CrossType.rel_comm X x.2.2 y.2.2).mp hxy
      simpa [hi.symm] using hyx
    · have hY : Y = true := by simpa [hi] using hc
      simpa [hi.symm] using hY

theorem coverAdj_irrefl {s t : Nat} (X : CrossType) (Y : Bool)
    (x : CoverVertex s t) : ¬ coverAdj X Y x x := by
  intro h
  rcases h with ⟨_, _, ha⟩ | ⟨hs, _⟩
  · exact ha rfl
  · exact hs rfl

/-- The graph specified by the connection matrix of Definition 1.6. -/
def coverGraph (s t : Nat) (X : CrossType) (Y : Bool) :
    SimpleGraph (CoverVertex s t) where
  Adj := coverAdj X Y
  symm := coverAdj_flip X Y
  loopless := coverAdj_irrefl X Y

/-- A disjoint union of `s` cliques with `t` vertices each. -/
def cliqueUnion (s t : Nat) : SimpleGraph (Fin s × Fin t) where
  Adj := fun x y => x.1 = y.1 ∧ x.2 ≠ y.2
  symm := by
    intro x y h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    intro x h
    exact h.2 rfl

theorem left_induced {s t : Nat} (X : CrossType) (Y : Bool)
    (i j : Fin s) (a b : Fin t) :
    (coverGraph s t X Y).Adj (left i a) (left j b) ↔
      (cliqueUnion s t).Adj (i, a) (j, b) := by
  simp [coverGraph, coverAdj, left, cliqueUnion]

theorem right_induced {s t : Nat} (X : CrossType) (Y : Bool)
    (i j : Fin s) (a b : Fin t) :
    (coverGraph s t X Y).Adj (right i a) (right j b) ↔
      (cliqueUnion s t).Adj (i, a) (j, b) := by
  simp [coverGraph, coverAdj, right, cliqueUnion]

theorem cross_diag_iff {s t : Nat} (X : CrossType) (Y : Bool)
    (i : Fin s) (a b : Fin t) :
    (coverGraph s t X Y).Adj (left i a) (right i b) ↔ X.rel a b := by
  simp [coverGraph, coverAdj, left, right]

theorem cross_off_iff {s t : Nat} (X : CrossType) (Y : Bool)
    (i j : Fin s) (a b : Fin t) (hij : i ≠ j) :
    (coverGraph s t X Y).Adj (left i a) (right j b) ↔ Y = true := by
  simp [coverGraph, coverAdj, left, right, hij]

theorem coverVertex_card (s t : Nat) :
    Fintype.card (CoverVertex s t) = 2 * s * t := by
  simp [CoverVertex, Fintype.card_prod, Nat.mul_assoc]

/-- The Taylor double of a complete graph has no cross-edges.
A diagonal matching is different: it adds a cross-edge at every coordinate. -/
theorem matching_not_taylor_clique {t : Nat} (a : Fin t) :
    (coverGraph 1 t .matching false).Adj (left (0 : Fin 1) a) (right 0 a) ∧
    ¬ (coverGraph 1 t .empty false).Adj (left (0 : Fin 1) a) (right 0 a) := by
  simp [cross_diag_iff, CrossType.rel]

/-- When the diagonal type is complete, every vertex on the second side
is adjacent to the selected vertex of its own clique, regardless of the
selection on other cliques. This matters for the proof of Claim 3.11. -/
theorem full_diag_hits_every_right {s t : Nat} (Y : Bool)
    (pick : Fin s → Fin t) (j : Fin s) (b : Fin t) :
    (coverGraph s t .full Y).Adj (left j (pick j)) (right j b) := by
  exact (cross_diag_iff .full Y j (pick j) b).2 trivial

end EPPAIII
