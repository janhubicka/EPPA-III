import EPPAIII.CliqueCovers.TransitiveHalfEdges
import EPPAIII.CliqueCovers.OutsideLiftTransport

/-!
# Equal internal edge counts in an arbitrary vertex-transitive host

Earlier, TransitiveHalfEdges proved the half-edge equality for a
graph explicitly labelled by Bool × V. Here we construct this
labelling from an arbitrary embedded induced copy e : V ↪ W and an
equivalence f from V onto the complement of e.

The result is the exact invariant edge-count bridge needed in the
one-partial and zero-partial cases of Lemma 3.7. It does not assume
that the host was originally split into labelled halves.
-/

namespace EPPAIII.CliqueCovers

/-- Glue an embedding of V into W and an equivalence from V
onto its complementary subtype into a full two-half equivalence. -/
noncomputable def balancedHostEquiv {V W : Type*} [Fintype W]
    (e : V ↪ W)
    (f : V ≃ {u : W // u ∈ finiteOutside e}) :
    (Bool × V) ≃ W := by
  classical
  let g : Bool × V → W :=
    fun x => if x.1 then (f x.2).val else e x.2
  have hInj : Function.Injective g := by
    rintro ⟨b,x⟩ ⟨c,y⟩ h
    cases b <;> cases c
    · have hEq : e x = e y := by simpa [g] using h
      have hxy : x = y := e.injective hEq
      simp [hxy]
    · have hEq : e x = (f y).val := by simpa [g] using h
      have hy : (f y).val ∉ Set.range e := by
        simpa [finiteOutside] using (f y).property
      exact False.elim (hy ⟨x, hEq⟩)
    · have hEq : (f x).val = e y := by simpa [g] using h
      have hx : (f x).val ∉ Set.range e := by
        simpa [finiteOutside] using (f x).property
      exact False.elim (hx ⟨y, hEq.symm⟩)
    · have hEq : (f x).val = (f y).val := by simpa [g] using h
      have hxy : x = y := f.injective (Subtype.ext hEq)
      simp [hxy]
  have hSurj : Function.Surjective g := by
    intro u
    by_cases hu : u ∈ Set.range e
    · obtain ⟨v,hv⟩ := hu
      refine ⟨(false,v), ?_⟩
      simpa [g] using hv
    · have huOutside : u ∈ finiteOutside e := by
        simpa [finiteOutside] using hu
      refine ⟨(true, f.symm ⟨u,huOutside⟩), ?_⟩
      simp [g]
  exact Equiv.ofBijective g ⟨hInj, hSurj⟩

@[simp] theorem balancedHostEquiv_false {V W : Type*} [Fintype W]
    (e : V ↪ W) (f : V ≃ {u : W // u ∈ finiteOutside e})
    (v : V) :
    balancedHostEquiv e f (false,v) = e v := by
  rfl

@[simp] theorem balancedHostEquiv_true {V W : Type*} [Fintype W]
    (e : V ↪ W) (f : V ≃ {u : W // u ∈ finiteOutside e})
    (v : V) :
    balancedHostEquiv e f (true,v) = (f v).val := by
  rfl

/-- Transport vertex transitivity through an equivalence of host
vertex types. -/
theorem transitive_comap_equiv {V W : Type*}
    (H : SimpleGraph W) (phi : V ≃ W)
    (hT : HasTransitiveGraphAutomorphisms H) :
    HasTransitiveGraphAutomorphisms (H.comap phi) := by
  intro x y
  obtain ⟨q, hq, hxy⟩ := hT (phi x) (phi y)
  let p : Equiv.Perm V := (phi.trans q).trans phi.symm
  refine ⟨p, ?_, ?_⟩
  · intro u v
    change H.Adj (phi u) (phi v) ↔
      H.Adj (phi (p u)) (phi (p v))
    have hu : phi (p u) = q (phi u) := by
      simp [p, Equiv.trans_apply]
    have hv : phi (p v) = q (phi v) := by
      simp [p, Equiv.trans_apply]
    rw [hu,hv]
    exact hq (phi u) (phi v)
  · apply phi.injective
    simp [p, Equiv.trans_apply, hxy]

/-- Equal internal edge numbers for any two equally sized halves
of a vertex-transitive finite host, regardless of its original
vertex type. The first half is an induced G, and the second half
is given by a genuine equivalence with the complement of e. -/
theorem arbitrary_host_outside_edge_count_eq_base
    {V W : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V)
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (f : V ≃ {u : W // u ∈ finiteOutside e})
    (hT : HasTransitiveGraphAutomorphisms H) :
    ((outsideInducedGraph H e).comap f).edgeSet.ncard =
      G.edgeSet.ncard := by
  classical
  let phi := balancedHostEquiv e f
  let Hsplit : SimpleGraph (Bool × V) := H.comap phi
  have hTransitive : HasTransitiveGraphAutomorphisms Hsplit :=
    transitive_comap_equiv H phi hT
  have hSide :=
    sideEdges_equal_of_transitive_graph Hsplit hTransitive
  have hSideIntrinsic :
      (sideGraph Hsplit false).edgeSet.ncard =
        (sideGraph Hsplit true).edgeSet.ncard := by
    have hEdges :
        (sideGraph Hsplit false).edgeFinset.card =
          (sideGraph Hsplit true).edgeFinset.card := by
      simpa only [sideEdgeCount] using hSide
    simpa only [← SimpleGraph.card_edgeSet,
      Set.fintypeCard_eq_ncard] using hEdges
  have hFalse :
      sideGraph Hsplit false = H.comap e := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hTrue :
      sideGraph Hsplit true =
        (outsideInducedGraph H e).comap f := by
    apply SimpleGraph.ext
    funext x y
    rfl
  have hSelected : H.comap e = G := by
    apply SimpleGraph.ext
    funext x y
    exact propext (he x y).symm
  rw [hFalse,hTrue,hSelected] at hSideIntrinsic
  exact hSideIntrinsic.symm

end EPPAIII.CliqueCovers
