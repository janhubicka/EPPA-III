import EPPAIII.CliqueCovers.Basic

/-!
# Formal EPPA interface for finite graphs

An induced embedding is fixed, so the exact embedding of the witness is part
of the theorem. A partial automorphism is represented by a permutation of
the finite base vertex type, restricted to a chosen finite domain. The
restriction viewpoint covers every partial graph isomorphism: any bijection
between two equally sized finite subsets extends to a permutation.

This is an interface for subsequent claims, NOT a proof of Lemma 3.7.
-/

namespace EPPAIII

/-- A permutation preserving the entire graph, in both directions. -/
def IsGraphAutomorphism {V : Type*} (H : SimpleGraph V)
    (f : Equiv.Perm V) : Prop :=
  ∀ u v : V, H.Adj u v ↔ H.Adj (f u) (f v)

/-- A partial automorphism of a graph, represented by the restriction
of a permutation to the given domain. -/
def IsPartialGraphAutomorphism {V : Type*} (G : SimpleGraph V)
    (D : Finset V) (f : Equiv.Perm V) : Prop :=
  ∀ u v : V, u ∈ D → v ∈ D → (G.Adj u v ↔ G.Adj (f u) (f v))

theorem graphAuto_restricts {V : Type*} (G : SimpleGraph V)
    (f : Equiv.Perm V) (hf : IsGraphAutomorphism G f) (D : Finset V) :
    IsPartialGraphAutomorphism G D f := by
  intro u v _ _
  exact hf u v

/-- An induced embedding of graphs on possibly different vertex types. -/
def IsInducedGraphEmbedding {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  ∀ u v : V, G.Adj u v ↔ H.Adj (e u) (e v)

/-- A fixed induced embedding is an EPPA embedding when every partial
automorphism of the base is the restriction of an automorphism of the host. -/
def IsEPPAEmbedding {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop :=
  IsInducedGraphEmbedding G H e ∧
  ∀ (D : Finset V) (p : Equiv.Perm V),
    IsPartialGraphAutomorphism G D p →
      ∃ (q : Equiv.Perm W),
        IsGraphAutomorphism H q ∧
        ∀ v : V, v ∈ D → q (e v) = e (p v)

/-- The canonical injection of the first collection of cliques. -/
def coverLeftEmbedding (s t : Nat) :
    (Fin s × Fin t) ↪ CoverVertex s t where
  toFun := fun v => (false, v)
  inj' := by
    intro u v h
    exact congrArg Prod.snd h

theorem coverLeftEmbedding_induced (s t : Nat) (X : CrossType) (Y : Bool) :
    IsInducedGraphEmbedding (cliqueUnion s t) (coverGraph s t X Y)
      (coverLeftEmbedding s t) := by
  intro u v
  rcases u with ⟨i, a⟩
  rcases v with ⟨j, b⟩
  exact (left_induced X Y i j a b).symm

/-- The precise target property in Lemma 3.7: EPPA for the designated
first half. This is a definition, not a theorem claiming it holds. -/
def CoverIsEPPA (s t : Nat) (X : CrossType) (Y : Bool) : Prop :=
  IsEPPAEmbedding (cliqueUnion s t) (coverGraph s t X Y)
    (coverLeftEmbedding s t)

end EPPAIII
