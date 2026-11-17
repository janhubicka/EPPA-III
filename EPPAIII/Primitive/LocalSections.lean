import EPPAIII.EPPA.Definitions

/-!
# Automorphism sections from EPPA

An induced graph on a selected set has its automorphism group as a quotient
of the subgroup of host automorphisms that preserve its image and fix the
specified anchors. This uses extensions of single automorphisms and imposes
no coherence condition on those extensions.
-/

namespace EPPAIII.Primitive

variable {V W : Type*}

def graphAutomorphisms (H : SimpleGraph W) : Subgroup (Equiv.Perm W) where
  carrier := {q | IsGraphAutomorphism H q}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' {q r} hq hr := fun x y => (hr x y).trans (hq (r x) (r y))
  inv_mem' {q} hq := by
    intro x y
    simpa using (hq (q.symm x) (q.symm y)).symm

def pointwiseGraphStabilizer (H : SimpleGraph W) (U : Set W) :
    Subgroup (graphAutomorphisms H) where
  carrier := {q | ∀ u ∈ U, q.val u = u}
  one_mem' := fun _ _ => rfl
  mul_mem' {q r} hq hr := by
    intro u hu
    change q.val (r.val u) = u
    rw [hr u hu, hq u hu]
  inv_mem' {q} hq := by
    intro u hu
    change q.val.symm u = u
    exact q.val.symm_apply_eq.mpr (hq u hu).symm

def setwiseGraphStabilizer (H : SimpleGraph W) (U T : Set W) :
    Subgroup (pointwiseGraphStabilizer H U) where
  carrier := {q | ∀ t, q.val.val t ∈ T ↔ t ∈ T}
  one_mem' := fun _ => Iff.rfl
  mul_mem' {q r} hq hr := fun t => (hq (r.val.val t)).trans (hr t)
  inv_mem' {q} hq := by
    intro t
    simpa using (hq (q.val.val.symm t)).symm

private def imageEmbedding (e : V ↪ W) (S : Set V) : S ↪ W :=
  (Function.Embedding.subtype (· ∈ S)).trans e

noncomputable def restrictToSelected
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e) (S : Set V) (T : Set W) :
    setwiseGraphStabilizer H T (Set.range (imageEmbedding e S)) →*
      graphAutomorphisms (G.induce S) := by
  let f := Equiv.ofInjective (imageEmbedding e S) (imageEmbedding e S).injective
  let action := fun q : setwiseGraphStabilizer H T (Set.range (imageEmbedding e S)) =>
    (f.trans (q.val.val.val.subtypePerm q.property)).trans f.symm
  have hAct (q : setwiseGraphStabilizer H T (Set.range (imageEmbedding e S))) (x : S) :
      e (action q x : S).val = q.val.val.val (e x) :=
    congrArg Subtype.val (f.apply_symm_apply (q.val.val.val.subtypePerm q.property (f x)))
  have hAuto (q : setwiseGraphStabilizer H T (Set.range (imageEmbedding e S))) :
      IsGraphAutomorphism (G.induce S) (action q) := by
    intro x y
    change G.Adj (↑x) (↑y) ↔ G.Adj (↑(action q x)) (↑(action q y))
    rw [he x y, he (action q x) (action q y), hAct q x, hAct q y]
    exact q.val.val.property (e x) (e y)
  refine { toFun := fun q => ⟨action q, hAuto q⟩, map_one' := ?_, map_mul' := ?_ }
  · apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply e.injective
    exact hAct 1 x
  · intro q r
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply e.injective
    change e (action (q * r) x : S).val = e (action q (action r x) : S).val
    rw [hAct (q * r), hAct q, hAct r]
    rfl

/-- The restriction to the selected graph is onto, so its automorphism
group is a section of the host pointwise stabilizer of the anchors. -/
theorem restrictToSelected_surjective [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (S : Set V) (U : Finset V)
    (hDisjoint : ∀ u ∈ U, u ∉ S)
    (hCompatible : ∀ (p : graphAutomorphisms (G.induce S)) (u : V), u ∈ U →
      ∀ x : S, G.Adj u x ↔ G.Adj u (p.val x)) :
    Function.Surjective (restrictToSelected G H e heppa.1 S (e '' (U : Set V))) := by
  classical
  letI := Fintype.ofFinite S
  intro p
  let p' : Equiv.Perm V := Equiv.Perm.ofSubtype p.val
  let D : Finset V := U ∪ Finset.univ.image (Subtype.val : S → V)
  have hOn (x : S) : p' x = ↑(p.val x) := Equiv.Perm.ofSubtype_apply_coe p.val x
  have hFix (u : V) (hu : u ∈ U) : p' u = u :=
    Equiv.Perm.ofSubtype_apply_of_not_mem p.val (hDisjoint u hu)
  have hPart : IsPartialGraphAutomorphism G D p' := by
    intro x y hx hy
    rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
    · rw [hFix x hx, hFix y hy]
    · obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hy
      rw [hFix x hx, hOn y]
      exact hCompatible p x hx y
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
      rw [hFix y hy, hOn x, G.adj_comm (↑x) y, G.adj_comm (↑(p.val x)) y]
      exact hCompatible p y hy x
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hy
      rw [hOn x, hOn y]
      exact p.property x y
  obtain ⟨q, hq, hExtend⟩ := heppa.2 D p' hPart
  have hFixQ (t : W) (ht : t ∈ e '' (U : Set V)) : q t = t := by
    obtain ⟨u, hu, rfl⟩ := ht
    simpa only [hFix u hu] using hExtend u (Finset.mem_union_left _ hu)
  have hOnQ (x : S) : q (e x) = e (p.val x) := by
    have hx : (x : V) ∈ D :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ x))
    simpa only [hOn x] using hExtend x hx
  have hSetQ (t : W) : q t ∈ Set.range (imageEmbedding e S) ↔
      t ∈ Set.range (imageEmbedding e S) := by
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := p.val.surjective x
      refine ⟨y, q.injective ?_⟩
      change q (e y) = q t
      rw [hOnQ y, hy]
      exact hx
    · rintro ⟨x, rfl⟩
      exact ⟨p.val x, (hOnQ x).symm⟩
  let q' : setwiseGraphStabilizer H (e '' (U : Set V)) (Set.range (imageEmbedding e S)) :=
    ⟨⟨⟨q, hq⟩, hFixQ⟩, hSetQ⟩
  refine ⟨q', ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Subtype.ext
  apply e.injective
  unfold restrictToSelected
  change e ((Equiv.ofInjective (imageEmbedding e S) (imageEmbedding e S).injective).symm
    (q.subtypePerm hSetQ ((Equiv.ofInjective (imageEmbedding e S) (imageEmbedding e S).injective) x))).val
      = e (p.val x)
  exact (congrArg Subtype.val
    ((Equiv.ofInjective (imageEmbedding e S) (imageEmbedding e S).injective).apply_symm_apply
      (q.subtypePerm hSetQ ((Equiv.ofInjective (imageEmbedding e S) (imageEmbedding e S).injective) x)))).trans
        (hOnQ x)

/-- An induced subgraph of either selected subconstituent yields a section
of the host automorphism group fixing the selected root. -/
theorem root_restrictToSelected_surjective [Finite V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (S : Set V)
    (hOutside : root ∉ S)
    (hConst : ∀ x ∈ S, ∀ y ∈ S, G.Adj root x ↔ G.Adj root y) :
    Function.Surjective (restrictToSelected G H e heppa.1 S {e root}) := by
  classical
  have hDisjoint : ∀ u ∈ ({root} : Finset V), u ∉ S := by
    intro u hu
    simpa [Finset.mem_singleton.mp hu] using hOutside
  have hImage : e '' (({root} : Finset V) : Set V) = {e root} := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Finset.mem_singleton.mp hu]
      exact Set.mem_singleton _
    · intro ht
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact ⟨root, Finset.mem_singleton_self _, rfl⟩
  have hSurjective := restrictToSelected_surjective G H e heppa S {root} hDisjoint (by
    intro p u hu x
    rw [Finset.mem_singleton.mp hu]
    exact hConst x x.property (p.val x) (p.val x).property)
  exact hImage ▸ hSurjective

end EPPAIII.Primitive
