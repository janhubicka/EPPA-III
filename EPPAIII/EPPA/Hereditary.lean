import EPPAIII.EPPA.Definitions

/-!
# EPPA embeddings are inherited by induced subgraphs of the base

This is the monotonicity step used in the final obstacle-hypergraph
discussion of EPPA III. The embedding and its image are part of the
statement; there is no appeal to abstract isomorphism classes.

A partial automorphism of a smaller induced base is a bijection between
two finite sets. Transport those finite maps along the selected induced
embedding into the larger base, extend that finite bijection to a full
permutation of the larger finite type, and use EPPA there.  No coherent
family of automorphism lifts is assumed.
-/

namespace EPPAIII

/-- The composite of two explicitly selected induced embeddings. -/
private def selectedCompositeEmbedding
    {U V W : Type*} (f : U ↪ V) (e : V ↪ W) : U ↪ W where
  toFun := fun u => e (f u)
  inj' := by
    intro u v h
    exact f.injective (e.injective h)

/-- If H is an EPPA witness for an induced embedded graph G, it is also
an EPPA witness for any induced subgraph F embedded into that copy of G.
All three embeddings are explicitly retained, so the conclusion concerns
the actual selected subgraph of H. -/
theorem eppa_embedding_of_induced_embedding
    {U V W : Type*}
    [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V]
    (F : SimpleGraph U) (G : SimpleGraph V) (H : SimpleGraph W)
    (f : U ↪ V) (e : V ↪ W)
    (hf : IsInducedGraphEmbedding F G f)
    (heppa : IsEPPAEmbedding G H e) :
    IsEPPAEmbedding F H (selectedCompositeEmbedding f e) := by
  classical
  constructor
  · intro u v
    exact (hf u v).trans (heppa.1 (f u) (f v))
  · intro D p hp
    let T := {u : U // u ∈ D}
    let src : T → V := fun u => f u.1
    let dst : T → V := fun u => f (p u.1)
    have hSrc : Function.Injective src := by
      intro u v h
      exact Subtype.ext (f.injective h)
    have hDst : Function.Injective dst := by
      intro u v h
      exact Subtype.ext (p.injective (f.injective h))
    obtain ⟨q,hq⟩ :=
      Equiv.Perm.exists_extending_pair src dst hSrc hDst
    let D' : Finset V := D.image f
    have hPartial : IsPartialGraphAutomorphism G D' q := by
      intro a b ha hb
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
      have hxq : q (f x) = f (p x) := hq ⟨x,hx⟩
      have hyq : q (f y) = f (p y) := hq ⟨y,hy⟩
      calc
        G.Adj (f x) (f y) ↔ F.Adj x y := (hf x y).symm
        _ ↔ F.Adj (p x) (p y) := hp x y hx hy
        _ ↔ G.Adj (f (p x)) (f (p y)) := hf (p x) (p y)
        _ ↔ G.Adj (q (f x)) (q (f y)) := by
          rw [hxq,hyq]
    obtain ⟨Q,hQ,hFix⟩ := heppa.2 D' q hPartial
    refine ⟨Q,hQ,?_⟩
    intro u hu
    have huImage : f u ∈ D' :=
      Finset.mem_image.mpr ⟨u,hu,rfl⟩
    have h := hFix (f u) huImage
    change Q (e (f u)) = e (f (p u))
    exact h.trans (congrArg e (hq ⟨u,hu⟩))

end EPPAIII
