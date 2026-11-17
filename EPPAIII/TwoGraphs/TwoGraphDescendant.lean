import EPPAIII.EPPA.BaseRelabel
import EPPAIII.TwoGraphs.AllTransversalEppa
import Mathlib.Logic.Equiv.Option

/-! # Homogeneous descendants of a homogeneous two-graph -/

namespace EPPAIII.TwoGraphs

open EPPAIII.BlockSystems
open EPPAIII.DoubleCover

/-- The switching representative with the indicated point isolated. -/
def rootSwitch {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) : SimpleGraph V :=
  taylorTransversalGraph G (fun x => decide (G.Adj r x))

/-- The descendant graph deletes the isolated point of its switched representative. -/
def rootDescendant {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r : V) :
    SimpleGraph {x : V // x ≠ r} :=
  (rootSwitch G r).induce {x | x ≠ r}

theorem rootSwitch_isolated {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r x : V) :
    ¬ (rootSwitch G r).Adj r x := by
  change ¬ (r ≠ x ∧ (G.Adj r x ↔ decide (G.Adj r r) = decide (G.Adj r x)))
  by_cases h : G.Adj r x <;> simp [h]

theorem rootDescendant_adj_iff {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (x y : {v : V // v ≠ r}) :
    (rootDescendant G r).Adj x y ↔ OddBaseTriple G r x y := by
  classical
  let C := rootSwitch G r
  let : DecidableRel C.Adj := taylorTransversalGraph_decidableRel G _
  change C.Adj x.val y.val ↔ OddBaseTriple G r x y
  have hOdd : OddBaseTriple C r x y ↔ C.Adj x.val y.val := by
    unfold OddBaseTriple
    have hx := rootSwitch_isolated G r x
    have hy : ¬ C.Adj y r := fun h => rootSwitch_isolated G r y h.symm
    simp [show ¬ C.Adj r x from hx, hy]
  exact hOdd.symm.trans (odd_triple_transversal_iff G (fun x => decide (G.Adj r x)) r x y)

/-- A nontrivial homogeneous two-graph has an odd and an even extension
of each pair of distinct points. -/
def HasBothParityExtensions {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ a b : V, a ≠ b →
    (∃ c, a ≠ c ∧ b ≠ c ∧ OddBaseTriple G a b c) ∧
    (∃ c, a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple G a b c)

/-- An adjacent pair of a clique union would extend to only odd triples. -/
theorem rootDescendant_not_cluster {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (x₀ : {x : V // x ≠ r}) (hPairs : HasBothParityExtensions G) :
    ¬ IsClusterGraph (rootDescendant G r) := by
  classical
  intro hCluster
  obtain ⟨b,hrb,hab,hOdd⟩ := (hPairs r x₀.val x₀.property.symm).1
  obtain ⟨c,hac,hbc,hEven⟩ := (hPairs x₀.val b hab).2
  let B : {x : V // x ≠ r} := ⟨b,hrb.symm⟩
  let C := rootSwitch G r
  let : DecidableRel C.Adj := taylorTransversalGraph_decidableRel G _
  have hAB : (rootDescendant G r).Adj x₀ B := (rootDescendant_adj_iff G r x₀ B).mpr hOdd
  have hAB' : C.Adj x₀.val b := hAB
  have hSame : C.Adj b c ↔ C.Adj c x₀.val := by
    by_cases hcr : c = r
    · subst c
      have h₁ : ¬ C.Adj b r := fun h => rootSwitch_isolated G r b h.symm
      have h₂ : ¬ C.Adj r x₀.val := rootSwitch_isolated G r x₀.val
      simp [h₁,h₂]
    let d : {x : V // x ≠ r} := ⟨c,hcr⟩
    change (rootDescendant G r).Adj B d ↔ (rootDescendant G r).Adj d x₀
    exact ⟨fun h => (hCluster x₀ B d hAB h (fun he => hac (congrArg Subtype.val he))).symm,
      fun h => (hCluster d x₀ B h hAB (fun he => hbc (congrArg Subtype.val he).symm)).symm⟩
  apply hEven
  apply (odd_triple_transversal_iff G (fun v => decide (G.Adj r v)) x₀.val b c).mp
  change OddBaseTriple C x₀.val b c
  by_cases h : C.Adj b c
  · simp [OddBaseTriple,hAB',h,hSame.mp h]
  · simp [OddBaseTriple,hAB',h,mt hSame.mpr h]

/-- A nonadjacent pair in a part of a complete multipartite graph would
extend to only even triples. -/
theorem rootDescendant_not_cocluster {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V) (x₀ : {x : V // x ≠ r}) (hPairs : HasBothParityExtensions G) :
    ¬ IsCoClusterGraph (rootDescendant G r) := by
  classical
  intro hCoCluster
  obtain ⟨b,hrb,hab,hEven⟩ := (hPairs r x₀.val x₀.property.symm).2
  obtain ⟨c,hac,hbc,hOdd⟩ := (hPairs x₀.val b hab).1
  let B : {x : V // x ≠ r} := ⟨b,hrb.symm⟩
  let C := rootSwitch G r
  let : DecidableRel C.Adj := taylorTransversalGraph_decidableRel G _
  have hAB : ¬ (rootDescendant G r).Adj x₀ B := mt (rootDescendant_adj_iff G r x₀ B).mp hEven
  have hAB' : ¬ C.Adj x₀.val b := hAB
  have hSame : ¬ C.Adj b c ↔ ¬ C.Adj c x₀.val := by
    by_cases hcr : c = r
    · subst c
      have h₁ : ¬ C.Adj b r := fun h => rootSwitch_isolated G r b h.symm
      have h₂ : ¬ C.Adj r x₀.val := rootSwitch_isolated G r x₀.val
      simp [h₁,h₂]
    let d : {x : V // x ≠ r} := ⟨c,hcr⟩
    change ¬ (rootDescendant G r).Adj B d ↔ ¬ (rootDescendant G r).Adj d x₀
    have hab' : x₀ ≠ B := fun he => hab (congrArg Subtype.val he)
    have hac' : x₀ ≠ d := fun he => hac (congrArg Subtype.val he)
    have hbc' : B ≠ d := fun he => hbc (congrArg Subtype.val he)
    constructor
    · intro h hAdj
      exact hCoCluster x₀ B d hab' hbc' hac' hAB h hAdj.symm
    · intro h hAdj
      exact hCoCluster d x₀ B hac'.symm hab' hbc'.symm h hAB hAdj.symm
  have h := (odd_triple_transversal_iff G (fun v => decide (G.Adj r v)) x₀.val b c).mpr hOdd
  change OddBaseTriple C x₀.val b c at h
  by_cases hBC : C.Adj b c
  · have hCA : C.Adj c x₀.val := Classical.byContradiction fun h => hSame.mpr h hBC
    simp [OddBaseTriple,hAB',hBC,hCA] at h
  · simp [OddBaseTriple,hAB',hBC,hSame.mp hBC] at h

/-- A two-graph automorphism induces a graph isomorphism on descendants. -/
def rootDescendantIso {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {r s : V} (σ : Equiv.Perm V) (hσ : IsTwoGraphAutomorphism G σ)
    (hRoot : σ r = s) : rootDescendant G r ≃g rootDescendant G s where
  toEquiv := σ.subtypeEquiv (fun x => σ.injective.ne_iff.symm.trans (by rw [hRoot]))
  map_rel_iff' := by
    intro x y
    rw [rootDescendant_adj_iff, rootDescendant_adj_iff]
    change OddBaseTriple G s (σ x) (σ y) ↔ OddBaseTriple G r x y
    rw [← hRoot]
    exact (hσ r x y).symm

/-- Homogeneity of the two-graph gives a homogeneous graph after isolating and
deleting any point. -/
theorem rootDescendant_homogeneous {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsHomogeneousTwoGraph G) (r : V) : IsHomogeneousGraph (rootDescendant G r) := by
  classical
  intro D p hp
  let σ₀ : Equiv.Perm V := Equiv.Perm.ofSubtype p
  let E : Finset V := insert r (D.image Subtype.val)
  have hr : σ₀ r = r := Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp)
  have hPartial : IsPartialGraphAutomorphism (rootSwitch G r) E σ₀ := by
    intro x y hx hy
    change x ∈ insert r (D.image Subtype.val) at hx
    change y ∈ insert r (D.image Subtype.val) at hy
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      have h₁ := rootSwitch_isolated G r y
      have h₂ := rootSwitch_isolated G r (σ₀ y)
      simp [hr,h₁,h₂]
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      have h₁ : ¬ (rootSwitch G r).Adj x r := fun h => rootSwitch_isolated G r x h.symm
      have h₂ : ¬ (rootSwitch G r).Adj (σ₀ x) r :=
        fun h => rootSwitch_isolated G r (σ₀ x) h.symm
      simp [hr,h₁,h₂]
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hy
    rw [show σ₀ u.val = (p u).val by exact Equiv.Perm.ofSubtype_apply_coe p u,
        show σ₀ v.val = (p v).val by exact Equiv.Perm.ofSubtype_apply_coe p v]
    exact hp u v hu hv
  have hTwo := partial_transversal_preserves_two_graph G (fun v => decide (G.Adj r v))
    E σ₀ hPartial
  obtain ⟨σ,hσ,hAgree⟩ := hG E σ₀ hTwo
  have hfix : σ r = r := (hAgree r (Finset.mem_insert_self r _)).trans hr
  let τ := rootDescendantIso G σ hσ hfix
  refine ⟨τ.toEquiv, fun _ _ => τ.map_rel_iff.symm, ?_⟩
  intro x hx
  apply Subtype.ext
  change σ x.val = (p x).val
  exact (hAgree x.val (Finset.mem_insert_of_mem (Finset.mem_image_of_mem Subtype.val hx))).trans
    (Equiv.Perm.ofSubtype_apply_coe p x)

/-- Descendants at any two points of a homogeneous two-graph are isomorphic. -/
theorem rootDescendant_iso_of_homogeneous {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsHomogeneousTwoGraph G) (r s : V) :
    Nonempty (rootDescendant G r ≃g rootDescendant G s) := by
  classical
  let p := Equiv.swap r s
  have hP : IsPartialTwoGraphAutomorphism G {r} p := by
    intro x hx y hy z hz
    rw [Finset.mem_singleton.mp hx, Finset.mem_singleton.mp hy, Finset.mem_singleton.mp hz]
    have h₁ := oddBaseTriple_repeated_false G r r r (Or.inl rfl)
    have h₂ := oddBaseTriple_repeated_false G (p r) (p r) (p r) (Or.inl rfl)
    simp [h₁,h₂]
  obtain ⟨σ,hσ,hAgree⟩ := hG {r} p hP
  exact ⟨rootDescendantIso G σ hσ ((hAgree r (by simp)).trans (Equiv.swap_apply_left r s))⟩

/-- A descendant automorphism extends by fixing the isolated point. -/
theorem rootDescendant_automorphism_extends {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (r : V) (p : Equiv.Perm {x : V // x ≠ r})
    (hp : IsGraphAutomorphism (rootDescendant G r) p) :
    IsTwoGraphAutomorphism G (Equiv.Perm.ofSubtype p) := by
  classical
  let C := rootSwitch G r
  let q : Equiv.Perm V := Equiv.Perm.ofSubtype p
  have hRoot : q r = r := Equiv.Perm.ofSubtype_apply_of_not_mem p (by simp)
  have hC : IsGraphAutomorphism C q := by
    intro x y
    by_cases hx : x = r
    · subst x
      have hy := rootSwitch_isolated G r y
      have hqy := rootSwitch_isolated G r (q y)
      change (rootSwitch G r).Adj r y ↔ (rootSwitch G r).Adj (q r) (q y)
      simp [hRoot,hy,hqy]
    by_cases hy : y = r
    · subst y
      have hx' : ¬ C.Adj x r := fun h => rootSwitch_isolated G r x h.symm
      have hqx : ¬ C.Adj (q x) r := fun h => rootSwitch_isolated G r (q x) h.symm
      simp [hRoot,hx',hqx]
    have h := hp ⟨x,hx⟩ ⟨y,hy⟩
    change C.Adj x y ↔ C.Adj (p ⟨x,hx⟩).val (p ⟨y,hy⟩).val at h
    rw [← Equiv.Perm.ofSubtype_apply_coe p ⟨x,hx⟩,
      ← Equiv.Perm.ofSubtype_apply_coe p ⟨y,hy⟩] at h
    exact h
  intro x y z
  let t : V → Bool := fun v => decide (G.Adj r v)
  have hParity := partial_transversal_preserves_two_graph G t {x,y,z} q
    (fun u v _ _ => hC u v)
  exact hParity x (by simp) y (by simp) z (by simp)

/-- Transitivity on points and homogeneity of the descendants imply
homogeneity of the associated two-graph. -/
theorem twoGraph_homogeneous_of_descendants {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hTrans : ∀ a b : V, ∃ q : Equiv.Perm V, IsTwoGraphAutomorphism G q ∧ q a = b)
    (hDescendants : ∀ r : V, IsHomogeneousGraph (rootDescendant G r)) :
    IsHomogeneousTwoGraph G := by
  classical
  intro D p hp
  by_cases hD : D.Nonempty
  · obtain ⟨a,ha⟩ := hD
    obtain ⟨q,hq,hqa⟩ := hTrans a (p a)
    let u : Equiv.Perm V := p.trans q.symm
    have hua : u a = a := by
      change q.symm (p a) = a
      rw [← hqa, q.symm_apply_apply]
    have hu : IsPartialTwoGraphAutomorphism G D u := by
      intro x hx y hy z hz
      have h := hq (u x) (u y) (u z)
      simpa [u] using (hp x hx y hy z hz).trans (by simpa [u] using h.symm)
    let E := D.subtype (fun x => x ≠ a)
    let v : Equiv.Perm {x : V // x ≠ a} :=
      u.subtypeEquiv (fun x => u.injective.ne_iff.symm.trans (by rw [hua]))
    have hv : IsPartialGraphAutomorphism (rootDescendant G a) E v := by
      intro x y hx hy
      have h := hu a ha x (Finset.mem_subtype.mp hx) y (Finset.mem_subtype.mp hy)
      rw [hua] at h
      rw [rootDescendant_adj_iff, rootDescendant_adj_iff]
      exact h
    obtain ⟨ρ,hρ,hAgree⟩ := hDescendants a E v hv
    let s : Equiv.Perm V := Equiv.Perm.ofSubtype ρ
    refine ⟨s.trans q, fun x y z => ?_, ?_⟩
    · exact (rootDescendant_automorphism_extends G a ρ hρ x y z).trans (hq (s x) (s y) (s z))
    · intro x hx
      by_cases hxa : x = a
      · subst x
        change q (s a) = p a
        rw [show s a = a from Equiv.Perm.ofSubtype_apply_of_not_mem ρ (by simp), hqa]
      · have h := hAgree ⟨x,hxa⟩ (Finset.mem_subtype.mpr hx)
        have h' : s x = u x := (Equiv.Perm.ofSubtype_apply_coe ρ ⟨x,hxa⟩).trans
          (congrArg Subtype.val h)
        change q (s x) = p x
        rw [h']
        exact q.apply_symm_apply (p x)
  · refine ⟨Equiv.refl V, fun _ _ _ => Iff.rfl, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hD]

/-- Add one isolated point, with no change to the other adjacencies. -/
def addIsolate {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | some a, some b => G.Adj a b
    | _, _ => False
  symm := ⟨by rintro (_ | _) (_ | _) h <;> first | exact h | exact h.symm⟩
  loopless := ⟨by rintro (_ | _) h <;> first | exact h | exact (G.ne_of_adj h rfl)⟩

/-- Descendant identification lifts to the normalized switching representative. -/
noncomputable def addIsolateIsoRootSwitch {V A : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : V} {J : SimpleGraph A} (φ : J ≃g rootDescendant G r) :
    addIsolate J ≃g rootSwitch G r := by
  classical
  let f : Option A ≃ V := (Equiv.optionSubtype r).symm φ.toEquiv
  refine ⟨f, ?_⟩
  rintro (_ | x) (_ | y)
  · simp [f,addIsolate]
  · simpa [f,addIsolate] using rootSwitch_isolated G r (φ y).val
  · simpa [f,addIsolate,SimpleGraph.adj_comm] using rootSwitch_isolated G r (φ x).val
  · change (rootSwitch G r).Adj (φ x).val (φ y).val ↔ J.Adj x y
    exact φ.map_rel_iff

/-- A base graph relabelling gives the corresponding Taylor-double relabelling. -/
def taylorIsoOfBaseIso {V A : Type*} {G : SimpleGraph V} {J : SimpleGraph A} (φ : J ≃g G) :
    taylorPairGraph J ≃g taylorPairGraph G where
  toEquiv := Equiv.prodCongr (Equiv.refl Bool) φ.toEquiv
  map_rel_iff' := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    change (φ x ≠ φ y ∧ (G.Adj (φ x) (φ y) ↔ i = j)) ↔
      (x ≠ y ∧ (J.Adj x y ↔ i = j))
    rw [φ.injective.ne_iff, φ.map_rel_iff]

/-- Flipping both labels of each of the switched fibres gives the old
Taylor double. -/
def taylorIsoOfSwitch {V : Type*} (G : SimpleGraph V) (t : V → Bool) :
    taylorPairGraph (taylorTransversalGraph G t) ≃g taylorPairGraph G where
  toEquiv :=
    { toFun := fun x => (Bool.xor x.1 (t x.2), x.2)
      invFun := fun x => (Bool.xor x.1 (t x.2), x.2)
      left_inv := by rintro ⟨b,x⟩; cases b <;> cases h : t x <;> simp [h,Bool.xor]
      right_inv := by rintro ⟨b,x⟩; cases b <;> cases h : t x <;> simp [h,Bool.xor] }
  map_rel_iff' := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    change (x ≠ y ∧ (G.Adj x y ↔ Bool.xor i (t x) = Bool.xor j (t y))) ↔
      (x ≠ y ∧ ((x ≠ y ∧ (G.Adj x y ↔ t x = t y)) ↔ i = j))
    by_cases hxy : x ≠ y
    · cases i <;> cases j <;> cases t x <;> cases t y <;>
        by_cases h : G.Adj x y <;> simp [Bool.xor,h,hxy]
    · simp [hxy]

/-- An identified descendant determines the Taylor host, with an explicit
map from the indicated model. -/
noncomputable def taylorIsoOfDescendant {V A : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : V} {J : SimpleGraph A} (φ : J ≃g rootDescendant G r) :
    taylorPairGraph (addIsolate J) ≃g taylorPairGraph G :=
  (taylorIsoOfBaseIso (addIsolateIsoRootSwitch G φ)).trans
    (taylorIsoOfSwitch G (fun v => decide (G.Adj r v)))

theorem taylorIsoOfDescendant_symm_snd {V A : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] {r : V} {J : SimpleGraph A} (φ : J ≃g rootDescendant G r)
    (p : Bool × V) :
    ((taylorIsoOfDescendant G φ).symm p).2 = (addIsolateIsoRootSwitch G φ).symm p.2 :=
  rfl

/-- A copy whose pairs all have an even triple extension cannot contain
both vertices of any Taylor fibre. -/
theorem taylor_fibre_projection_injective {V A : Type*} (J : SimpleGraph A)
    [DecidableRel J.Adj] (G : SimpleGraph V) (e : A ↪ Bool × V)
    (hEmb : IsInducedGraphEmbedding J (taylorPairGraph G) e)
    (hEven : ∀ a b : A, a ≠ b → ∃ c, a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple J a b c) :
    Function.Injective (fun a => (e a).2) := by
  classical
  intro a b hab
  by_contra hne
  obtain ⟨c,hac,hbc,hParity⟩ := hEven a b hne
  rcases ea : e a with ⟨i,x⟩
  rcases eb : e b with ⟨j,y⟩
  rcases ec : e c with ⟨k,z⟩
  change (e a).2 = (e b).2 at hab
  rw [ea,eb] at hab
  change x = y at hab
  subst y
  have hij : i ≠ j := by
    intro h
    apply hne
    apply e.injective
    rw [ea,eb,h]
  have hxz : x ≠ z := by
    intro h
    subst z
    have hik : i ≠ k := by
      intro h
      apply hac
      apply e.injective
      rw [ea,ec,h]
    have hjk : j ≠ k := by
      intro h
      apply hbc
      apply e.injective
      rw [eb,ec,h]
    cases i <;> cases j <;> cases k <;> simp_all
  have hAB := hEmb a b
  have hBC := hEmb b c
  have hCA := hEmb c a
  rw [ea,eb] at hAB
  rw [eb,ec] at hBC
  rw [ec,ea] at hCA
  change J.Adj a b ↔ (x ≠ x ∧ (G.Adj x x ↔ i = j)) at hAB
  change J.Adj b c ↔ (x ≠ z ∧ (G.Adj x z ↔ j = k)) at hBC
  change J.Adj c a ↔ (z ≠ x ∧ (G.Adj z x ↔ k = i)) at hCA
  simp only [ne_self_iff_false, false_and, iff_false] at hAB
  rw [G.adj_comm z x] at hCA
  apply hParity
  cases i <;> cases j <;> cases k <;>
    by_cases h : G.Adj x z <;> simp_all [OddBaseTriple,Bool.xor]

/-- Every induced copy that meets each fibre once is an EPPA embedding in
the Taylor host of a homogeneous two-graph. -/
theorem taylor_eppa_of_induced_transversal {V A : Type*}
    [Fintype V] [Fintype A] (J : SimpleGraph A)
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : A ↪ Bool × V)
    (hEmb : IsInducedGraphEmbedding J (taylorPairGraph G) e)
    (hHom : IsHomogeneousTwoGraph G) (hBij : Function.Bijective (fun a => (e a).2)) :
    IsEPPAEmbedding J (taylorPairGraph G) e := by
  classical
  let φ : A ≃ V := Equiv.ofBijective (fun a => (e a).2) hBij
  let t : V → Bool := fun v => (e (φ.symm v)).1
  have hEq : relabelEmbedding (taylorTransversalEmbedding t) φ = e := by
    apply Function.Embedding.ext
    intro a
    apply Prod.ext
    · change (e (φ.symm (φ a))).1 = (e a).1
      rw [φ.symm_apply_apply]
    · rfl
  have hBase (a b : A) :
      J.Adj a b ↔ (taylorTransversalGraph G t).Adj (φ a) (φ b) := by
    change J.Adj a b ↔ (taylorPairGraph G).Adj
      (relabelEmbedding (taylorTransversalEmbedding t) φ a)
      (relabelEmbedding (taylorTransversalEmbedding t) φ b)
    rw [hEq]
    exact hEmb a b
  rw [← hEq]
  exact eppa_relabel_base _ _ _ (homogeneous_two_graph_all_transversals_eppa G hHom t) φ J hBase

/-- An induced copy of the base order is a transversal if all its pairs
extend to even triples. -/
theorem taylor_eppa_of_induced_copy_with_even_extensions {V A : Type*}
    [Fintype V] [Fintype A] (J : SimpleGraph A) [DecidableRel J.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : A ↪ Bool × V)
    (hEmb : IsInducedGraphEmbedding J (taylorPairGraph G) e)
    (hHom : IsHomogeneousTwoGraph G) (hCard : Fintype.card A = Fintype.card V)
    (hEven : ∀ a b : A, a ≠ b → ∃ c, a ≠ c ∧ b ≠ c ∧ ¬ OddBaseTriple J a b c) :
    IsEPPAEmbedding J (taylorPairGraph G) e :=
  taylor_eppa_of_induced_transversal J G e hEmb hHom
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨taylor_fibre_projection_injective J G e hEmb hEven, hCard⟩)

end EPPAIII.TwoGraphs
