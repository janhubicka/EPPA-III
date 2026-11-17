import EPPAIII.EPPA.BaseRelabel

/-!
# EPPA on the subconstituents at a selected vertex

The first graph is induced on neighbours of the root. The second is induced
on its distinct nonneighbours, and agrees with the distance-two
subconstituent when the host has diameter at most two.
-/

namespace EPPAIII.Primitive

def localGraph {V : Type*} (H : SimpleGraph V) (root : V) :=
  H.induce (H.neighborSet root)

def nonlocalGraph {V : Type*} (H : SimpleGraph V) (root : V) :=
  H.induce {x | root ≠ x ∧ ¬ H.Adj root x}

/-- A host isomorphism maps local constituents at corresponding roots. -/
def localIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (r : V) : localGraph G r ≃g localGraph H (φ r) where
  toEquiv := φ.mapNeighborSet r
  map_rel_iff' := φ.map_adj_iff

/-- A host isomorphism maps nonlocal constituents at corresponding roots. -/
def nonlocalIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) (r : V) : nonlocalGraph G r ≃g nonlocalGraph H (φ r) where
  toEquiv := φ.toEquiv.subtypeEquiv fun x =>
    and_congr (not_congr φ.injective.eq_iff.symm) φ.map_adj_iff.symm.not
  map_rel_iff' := φ.map_adj_iff

/-- Complementation exchanges neighbours with distinct nonneighbours. -/
def localComplIso {V : Type*} (G : SimpleGraph V) (r : V) :
    localGraph Gᶜ r ≃g (nonlocalGraph G r)ᶜ where
  toEquiv := Equiv.refl _
  map_rel_iff' := and_congr (not_congr Subtype.val_injective.eq_iff.symm) Iff.rfl

/-- Complementation exchanges distinct nonneighbours with neighbours. -/
def nonlocalComplIso {V : Type*} (G : SimpleGraph V) (r : V) :
    nonlocalGraph Gᶜ r ≃g (localGraph G r)ᶜ where
  toEquiv := (Equiv.refl V).subtypeEquiv fun x => by
    change (r ≠ x ∧ ¬ (r ≠ x ∧ ¬ G.Adj r x)) ↔ G.Adj r x
    exact ⟨fun ⟨hne, h⟩ => Classical.byContradiction fun hn => h ⟨hne, hn⟩,
      fun h => ⟨h.ne, fun hn => hn.2 h⟩⟩
  map_rel_iff' := by
    intro a b
    change (_ ≠ _ ∧ ¬ G.Adj a.val b.val) ↔
      (a.val ≠ b.val ∧ ¬ G.Adj a.val b.val)
    exact and_congr (not_congr ⟨fun h => congrArg (fun x : G.neighborSet r => x.val) h,
      fun h => Subtype.ext h⟩) Iff.rfl

/-- Restrict an embedding to the chosen sets on two vertex types. -/
def restrictEmbedding {V W : Type*} (e : V ↪ W) {S : Set V} {T : Set W}
    (he : ∀ x ∈ S, e x ∈ T) : S ↪ T where
  toFun x := ⟨e x, he x x.property⟩
  inj' _ _ h := Subtype.ext (e.injective (congrArg Subtype.val h))

/-- Root fixation gives EPPA on an induced adjacency class. -/
private theorem eppa_induce_at_root
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) (root : V)
    {S : Set V} {T : Set W} (he : ∀ x ∈ S, e x ∈ T)
    (hOutside : root ∉ S) (hConst : ∀ x ∈ S, ∀ y ∈ S, G.Adj root x ↔ G.Adj root y)
    (hInv : ∀ q : Equiv.Perm W, IsGraphAutomorphism H q → q (e root) = e root →
      ∀ x, q x ∈ T ↔ x ∈ T) :
    IsEPPAEmbedding (G.induce S) (H.induce T) (restrictEmbedding e he) := by
  classical
  constructor
  · intro x y
    exact heppa.1 x y
  · intro D p hp
    let p' : Equiv.Perm V := Equiv.Perm.ofSubtype p
    have hOn (x : S) : p' x = ↑(p x) := Equiv.Perm.ofSubtype_apply_coe p x
    have hFix : p' root = root := Equiv.Perm.ofSubtype_apply_of_not_mem p hOutside
    let D' := insert root (D.image Subtype.val)
    have hPart : IsPartialGraphAutomorphism G D' p' := by
      intro x y hx hy
      rcases Finset.mem_insert.mp hx with hxr | hxs <;>
        rcases Finset.mem_insert.mp hy with hyr | hys
      · subst x
        subst y
        rw [hFix]
      · subst x
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hys
        rw [hFix, hOn b]
        exact hConst _ b.property _ (p b).property
      · subst y
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxs
        rw [hFix, hOn a, G.adj_comm (↑a) root, G.adj_comm (↑(p a)) root]
        exact hConst _ a.property _ (p a).property
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hxs
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hys
        rw [hOn a, hOn b]
        exact hp a b ha hb
    obtain ⟨q, hq, hExtend⟩ := heppa.2 D' p' hPart
    have hqFix : q (e root) = e root := by
      simpa only [hFix] using hExtend root (Finset.mem_insert_self _ _)
    let q' := q.subtypePerm (hInv q hq hqFix)
    refine ⟨q', fun x y => hq x y, ?_⟩
    intro x hx
    apply Subtype.ext
    change q (e x) = e (p x)
    have hx' : (x : V) ∈ D' := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hx)
    simpa only [hOn x] using hExtend x hx'

/-- Lemma eppaneighbor for the first subconstituent. -/
theorem local_eppa {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) (root : V) :
    IsEPPAEmbedding (localGraph G root) (localGraph H (e root))
      (restrictEmbedding e (fun x hx => (heppa.1 root x).mp hx)) := by
  apply eppa_induce_at_root G H e heppa root
  · exact G.loopless.irrefl root
  · exact fun _ hx _ hy => iff_of_true hx hy
  · intro q hq hFix x
    change H.Adj (e root) (q x) ↔ H.Adj (e root) x
    have hh := hq (e root) x
    rw [hFix] at hh
    exact hh.symm

/-- Lemma eppaneighbor for the second subconstituent. -/
theorem nonlocal_eppa {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W) (heppa : IsEPPAEmbedding G H e) (root : V) :
    IsEPPAEmbedding (nonlocalGraph G root) (nonlocalGraph H (e root))
      (restrictEmbedding e (fun x hx =>
        ⟨e.injective.ne hx.1, (heppa.1 root x).not.mp hx.2⟩)) := by
  apply eppa_induce_at_root G H e heppa root
  · exact fun h => h.1 rfl
  · exact fun _ hx _ hy => iff_of_false hx.2 hy.2
  · intro q hq hFix x
    change (e root ≠ q x ∧ ¬ H.Adj (e root) (q x)) ↔
      (e root ≠ x ∧ ¬ H.Adj (e root) x)
    have hh := hq (e root) x
    have hNe : q (e root) ≠ q x ↔ e root ≠ x :=
      ⟨fun h hEq => h (congrArg q hEq), fun h hEq => h (q.injective hEq)⟩
    rw [hFix] at hh hNe
    exact and_congr hNe hh.not.symm

end EPPAIII.Primitive
