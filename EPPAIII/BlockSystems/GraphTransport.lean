import EPPAIII.BlockSystems.CanonicalPairs
import EPPAIII.DoubleCover.CompleteTaylor

/-!
# Relabelling an EPPA host by its canonical paired-fibre coordinates

All mathematical structure is transported along an actual equivalence
φ : Bool × V ≃ W. The graph on Bool × V is the pullback of H.
If φ(false,x) = e x, the EPPA embedding transports.
If φ maps each fibre to an invariant block, and the base meets blocks
injectively, the invariant partition transports to HasInvariantPairs.

No automorphism extension is chosen coherently: automorphisms are only
conjugated through the verified equivalence.
-/

namespace EPPAIII.BlockSystems

/-- Graph relabelling along a bijection. -/
def pullbackGraph {X W : Type*}
    (H : SimpleGraph W) (φ : X ≃ W) : SimpleGraph X where
  Adj u v := H.Adj (φ u) (φ v)
  symm := by
    constructor
    intro u v h
    exact (H.adj_comm (φ u) (φ v)).mp h
  loopless := by
    constructor
    intro u h
    exact (H.irrefl (φ u)) h

/-- EPPA is invariant under relabelling of the host along an
equivalence which carries the canonical bottom embedding to e. -/
theorem eppa_pullback_bottom {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (φ : Bool × V ≃ W)
    (hBottom : ∀ x : V, φ (false,x) = e x) :
    IsEPPAEmbedding G (pullbackGraph H φ)
      (DoubleCover.bottomEmbedding V) := by
  classical
  constructor
  · intro x y
    change G.Adj x y ↔ H.Adj (φ (false,x)) (φ (false,y))
    simpa only [hBottom x, hBottom y] using heppa.1 x y
  · intro D p hPartial
    obtain ⟨q,hq,hExt⟩ := heppa.2 D p hPartial
    let q' : Equiv.Perm (Bool × V) :=
      (φ.trans q).trans φ.symm
    have hConj (z : Bool × V) : φ (q' z) = q (φ z) := by
      simp [q']
    refine ⟨q', ?_, ?_⟩
    · intro z t
      change H.Adj (φ z) (φ t) ↔
        H.Adj (φ (q' z)) (φ (q' t))
      simpa only [hConj z, hConj t] using hq (φ z) (φ t)
    · intro x hx
      change q' (false,x) = (false,p x)
      apply φ.injective
      calc
        φ (q' (false,x)) = q (φ (false,x)) := hConj _
        _ = q (e x) := by rw [hBottom x]
        _ = e (p x) := hExt x hx
        _ = φ (false,p x) := (hBottom (p x)).symm

/-- A block-labelling that identifies every canonical pair and
distinguishes distinct base vertices provides the exact invariance
predicate used by the Taylor-double theorem. -/
theorem invariant_pairs_of_pullback {V W B : Type*}
    [Fintype V]
    (H : SimpleGraph W) (e : V ↪ W)
    (block : W → B) (hBlocks : InvariantBlockMap H block)
    (hBlockInject : Function.Injective
      (fun x : V => block (e x)))
    (φ : Bool × V ≃ W)
    (hPairBlock : ∀ (b : Bool) (x : V),
      block (φ (b,x)) = block (e x)) :
    DoubleCover.HasInvariantPairs (pullbackGraph H φ) := by
  classical
  have hPair (u v : Bool × V) :
      u.2 = v.2 ↔ block (φ u) = block (φ v) := by
    rcases u with ⟨bu,x⟩
    rcases v with ⟨bv,y⟩
    change x = y ↔ block (φ (bu,x)) = block (φ (bv,y))
    rw [hPairBlock bu x, hPairBlock bv y]
    exact ⟨fun h => congrArg (fun z => block (e z)) h, fun h => hBlockInject h⟩
  intro q' hq'
  let qW : Equiv.Perm W :=
    (φ.symm.trans q').trans φ
  have hBack (u : Bool × V) :
      qW (φ u) = φ (q' u) := by
    simp [qW]
  have hW : IsGraphAutomorphism H qW := by
    intro w z
    have hh := hq' (φ.symm w) (φ.symm z)
    change H.Adj (φ (φ.symm w)) (φ (φ.symm z)) ↔
      H.Adj (φ (q' (φ.symm w))) (φ (q' (φ.symm z))) at hh
    simpa [qW] using hh
  have hOrbit (u v : Bool × V) :
      u.2 = v.2 ↔ (q' u).2 = (q' v).2 := by
    calc
      u.2 = v.2 ↔ block (φ u) = block (φ v) := hPair u v
      _ ↔ block (qW (φ u)) = block (qW (φ v)) :=
        hBlocks qW hW (φ u) (φ v)
      _ ↔ block (φ (q' u)) = block (φ (q' v)) := by
        rw [hBack u, hBack v]
      _ ↔ (q' u).2 = (q' v).2 := (hPair (q' u) (q' v)).symm
  let f : V → V := fun x => (q' (false,x)).2
  have hInj : Function.Injective f := by
    intro x y hh
    exact (hOrbit (false,x) (false,y)).mpr hh
  have hSurj : Function.Surjective f :=
    Finite.surjective_of_injective hInj
  let σ : Equiv.Perm V := Equiv.ofBijective f ⟨hInj,hSurj⟩
  refine ⟨σ, ?_⟩
  intro b x
  cases b with
  | false =>
      rfl
  | true =>
      have hh := (hOrbit (false,x) (true,x)).mp rfl
      exact hh.symm

end EPPAIII.BlockSystems
