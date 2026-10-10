import EPPAIII.DoubleCover.LayerRigidity
import EPPAIII.EPPA.ProfileAction

/-!
# Two-point EPPA action on an invariant fibre system

A graph on `Bool × V` has an invariant pair system if every graph
automorphism induces a permutation of the second coordinates.
The selected copy of the base graph is `{false} × V`.

Unlike a mere abstract orbit assumption, this file derives the
two-point orbit property from the *actual EPPA embedding*. It then
establishes the uniformity of all three free entries of the
2×2 inter-fibre adjacency matrices, together with their mate images.

The later equal-edge-count and non-homogeneity steps of Lemma 3.3
remain separate proof obligations.
-/

namespace EPPAIII.DoubleCover

/-- The natural bottom-layer embedding into a paired-fibre graph. -/
def bottomEmbedding (V : Type*) : V ↪ Bool × V where
  toFun := fun x => (false, x)
  inj' := by
    intro x y h
    exact congrArg Prod.snd h

/-- All automorphisms preserve the designated system of paired fibres. -/
def HasInvariantPairs {V : Type*} (H : SimpleGraph (Bool × V)) : Prop :=
  ∀ q : Equiv.Perm (Bool × V), IsGraphAutomorphism H q →
    ∃ σ : Equiv.Perm V,
      ∀ b : Bool, ∀ x : V, (q (b, x)).2 = σ x

/-- Given two injections of a two-element set into V, extend the
prescribed point mapping to a global permutation of V. -/
theorem exists_perm_of_two_maps {V : Type*}
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v) :
    ∃ p : Equiv.Perm V, p x = u ∧ p y = v := by
  classical
  let f : Equiv.Perm V := Equiv.swap x u
  have hfx : f x = u := by
    simp [f]
  have hfy : f y ≠ u := by
    intro h
    apply hxy
    exact (f.injective (h.trans hfx.symm)).symm
  let g : Equiv.Perm V := Equiv.swap (f y) v
  have hgu : g u = u := by
    change (Equiv.swap (f y) v) u = u
    apply Equiv.swap_apply_of_ne_of_ne
    · exact Ne.symm hfy
    · exact huv
  refine ⟨f.trans g, ?_, ?_⟩
  · change g (f x) = u
    rw [hfx]
    exact hgu
  · change g (f y) = v
    simp [g]

/-- The two-point partial automorphism is the restriction of the
permutation supplied by the preceding elementary construction. -/
theorem partial_of_two_maps {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (x y u v : V)
    (hxy : x ≠ y) (huv : u ≠ v)
    (hadj : G.Adj x y ↔ G.Adj u v) :
    ∃ p : Equiv.Perm V,
      p x = u ∧ p y = v ∧
      IsPartialGraphAutomorphism G ({x,y} : Finset V) p := by
  obtain ⟨p, hx, hy⟩ := exists_perm_of_two_maps x y u v hxy huv
  refine ⟨p, hx, hy, ?_⟩
  intro a b ha hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · simp [ha, hb, hx]
  · simpa [ha, hb, hx, hy] using hadj
  · simpa [ha, hb, hy, hx] using
      ((G.adj_comm y x).trans (hadj.trans (G.adj_comm u v)))
  · simp [ha, hb, hy]

/-- A fibre-preserving permutation sends the mate of a bottom vertex
to the mate of the image of that bottom vertex. -/
theorem top_image_of_bottom_image {V : Type*}
    (q : Equiv.Perm (Bool × V)) (σ : Equiv.Perm V)
    (hσ : ∀ b : Bool, ∀ x : V, (q (b,x)).2 = σ x)
    (x u : V) (hbot : q (false,x) = (false,u)) :
    q (true,x) = (true,u) := by
  have hfirst : (q (true,x)).1 = true := by
    have h := fibre_layer_complement q σ hσ x
    simpa [hbot] using h
  have hs : σ x = u := by
    calc
      σ x = (q (false,x)).2 := (hσ false x).symm
      _ = u := congrArg Prod.snd hbot
  have hsecond : (q (true,x)).2 = u := (hσ true x).trans hs
  exact Prod.ext hfirst hsecond

/-- **Two-point EPPA transfer.** Given any two ordered pairs of
distinct vertices of the same adjacency type, an automorphism of H
maps each bottom vertex and its mate to the corresponding target.

The witness is a genuine graph automorphism supplied by EPPA;
the global permutation of the base is constructed explicitly. -/
theorem eppa_maps_two_fibres {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hadj : G.Adj x y ↔ G.Adj u v) :
    ∃ q : Equiv.Perm (Bool × V),
      IsGraphAutomorphism H q ∧
      q (false,x) = (false,u) ∧ q (false,y) = (false,v) ∧
      q (true,x) = (true,u) ∧ q (true,y) = (true,v) := by
  classical
  obtain ⟨p,hx,hy,hPartial⟩ :=
    partial_of_two_maps G x y u v hxy huv hadj
  obtain ⟨q,hq,hExt⟩ := heppa.2 ({x,y} : Finset V) p hPartial
  have hbotx : q (false,x) = (false,u) := by
    have h := hExt x (by simp)
    change q (false,x) = (false,p x) at h
    simpa [hx] using h
  have hboty : q (false,y) = (false,v) := by
    have h := hExt y (by simp)
    change q (false,y) = (false,p y) at h
    simpa [hy] using h
  obtain ⟨σ,hσ⟩ := hPairs q hq
  exact ⟨q,hq,hbotx,hboty,
    top_image_of_bottom_image q σ hσ x u hbotx,
    top_image_of_bottom_image q σ hσ y v hboty⟩

/-- The three unspecified entries of the fibre-pair adjacency
matrix depend only on whether the two base vertices are adjacent. -/
theorem eppa_uniform_pair_entries {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y u v : V) (hxy : x ≠ y) (huv : u ≠ v)
    (hadj : G.Adj x y ↔ G.Adj u v) :
    (H.Adj (false,x) (true,y) ↔ H.Adj (false,u) (true,v)) ∧
    (H.Adj (true,x) (false,y) ↔ H.Adj (true,u) (false,v)) ∧
    (H.Adj (true,x) (true,y) ↔ H.Adj (true,u) (true,v)) := by
  obtain ⟨q,hq,hbx,hby,htx,hty⟩ :=
    eppa_maps_two_fibres G H heppa hPairs x y u v hxy huv hadj
  constructor
  · simpa [hbx, hty] using hq (false,x) (true,y)
  constructor
  · simpa [htx, hby] using hq (true,x) (false,y)
  · simpa [htx, hty] using hq (true,x) (true,y)

/-- Reversing any ordered pair forces equality of the two
off-diagonal entries in its symmetric 2×2 adjacency matrix. -/
theorem eppa_cross_symmetric {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y : V) (hxy : x ≠ y) :
    H.Adj (false,x) (true,y) ↔
      H.Adj (true,x) (false,y) := by
  have hSwap :=
    (eppa_uniform_pair_entries G H heppa hPairs
       x y y x hxy hxy.symm (G.adj_comm x y)).1
  calc
    H.Adj (false,x) (true,y) ↔ H.Adj (false,y) (true,x) := hSwap
    _ ↔ H.Adj (true,x) (false,y) := H.adj_comm (false,y) (true,x)

end EPPAIII.DoubleCover
