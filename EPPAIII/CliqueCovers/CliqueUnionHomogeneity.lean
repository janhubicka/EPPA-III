import EPPAIII.DoubleCover.RigidLayerHomogeneity
import EPPAIII.CliqueCovers.Basic

/-!
# Homogeneity of a disjoint union of equally sized cliques

The two-stage permutation extension is constructive at the level of
finite injections: first extend the map on clique indices, then extend
the coordinate maps inside each clique. No graph classification, EPPA
host, or transitivity is assumed for this canonical graph model.

For an arbitrary transitive cluster graph, a separate isomorphism
with such a model must still be constructed.
-/

namespace EPPAIII.CliqueCovers

/-- Every disjoint union of equally sized finite cliques is homogeneous,
including empty and singleton cases. -/
theorem cliqueUnion_isHomogeneous (s t : ℕ) :
    EPPAIII.DoubleCover.IsHomogeneousGraph (cliqueUnion s t) := by
  classical
  intro D p hp
  let I : Finset (Fin s) :=
    Finset.univ.filter (fun i => ∃ a : Fin t, (i,a) ∈ D)
  have hI (i : Fin s) : i ∈ I ↔ ∃ a : Fin t, (i,a) ∈ D := by
    simp [I]
  let rep (i : {i : Fin s // i ∈ I}) : Fin t :=
    Classical.choose ((hI i.1).mp i.2)
  have hrep (i : {i : Fin s // i ∈ I}) :
      (i.1,rep i) ∈ D :=
    Classical.choose_spec ((hI i.1).mp i.2)
  have hFirst (i : Fin s) (a b : Fin t)
      (ha : (i,a) ∈ D) (hb : (i,b) ∈ D) :
      (p (i,a)).1 = (p (i,b)).1 := by
    by_cases hab : a = b
    · subst b
      rfl
    · have hadj : (cliqueUnion s t).Adj (i,a) (i,b) :=
        ⟨rfl,hab⟩
      exact ((hp (i,a) (i,b) ha hb).mp hadj).1
  let f : {i : Fin s // i ∈ I} → Fin s := Subtype.val
  let g : {i : Fin s // i ∈ I} → Fin s :=
    fun i => (p (i.1,rep i)).1
  have hgInj : Function.Injective g := by
    intro i j hij
    by_contra hneq
    have hDifferent : i.1 ≠ j.1 :=
      fun h => hneq (Subtype.ext h)
    have hVertexNE : (i.1,rep i) ≠ (j.1,rep j) :=
      fun h => hDifferent (congrArg Prod.fst h)
    have hImageNE : p (i.1,rep i) ≠ p (j.1,rep j) :=
      p.injective.ne hVertexNE
    have hNotAdj : ¬ (cliqueUnion s t).Adj
        (i.1,rep i) (j.1,rep j) := by
      intro h
      exact hDifferent h.1
    have hImageNotAdj : ¬ (cliqueUnion s t).Adj
        (p (i.1,rep i)) (p (j.1,rep j)) := by
      intro h
      exact hNotAdj ((hp (i.1,rep i) (j.1,rep j)
        (hrep i) (hrep j)).mpr h)
    have hSecondNE :
        (p (i.1,rep i)).2 ≠ (p (j.1,rep j)).2 := by
      intro hsecond
      apply hImageNE
      exact Prod.ext hij hsecond
    exact hImageNotAdj ⟨hij,hSecondNE⟩
  obtain ⟨σ,hσ⟩ :=
    Equiv.Perm.exists_extending_pair f g Subtype.val_injective hgInj
  have hσCorrect (i : Fin s) (a : Fin t) (ha : (i,a) ∈ D) :
      σ i = (p (i,a)).1 := by
    have hi : i ∈ I := (hI i).mpr ⟨a,ha⟩
    let k : {i : Fin s // i ∈ I} := ⟨i,hi⟩
    have h := hσ k
    change σ i = (p (i,rep k)).1 at h
    exact h.trans (hFirst i (rep k) a (hrep k) ha)
  have hLocal (i : Fin s) :
      ∃ π : Equiv.Perm (Fin t), ∀ a : Fin t,
        (i,a) ∈ D → π a = (p (i,a)).2 := by
    let A : Type := {a : Fin t // (i,a) ∈ D}
    let fA : A → Fin t := Subtype.val
    let gA : A → Fin t := fun a => (p (i,a.1)).2
    have hgA : Function.Injective gA := by
      intro a b hab
      apply Subtype.ext
      have hfull : p (i,a.1) = p (i,b.1) := by
        apply Prod.ext
        · exact (hσCorrect i a.1 a.2).symm.trans
            (hσCorrect i b.1 b.2)
        · exact hab
      exact congrArg Prod.snd (p.injective hfull)
    obtain ⟨π,hπ⟩ :=
      Equiv.Perm.exists_extending_pair fA gA
        Subtype.val_injective hgA
    refine ⟨π,?_⟩
    intro a ha
    simpa [fA,gA] using hπ (⟨a,ha⟩ : A)
  let π (i : Fin s) : Equiv.Perm (Fin t) :=
    Classical.choose (hLocal i)
  have hπCorrect (i : Fin s) (a : Fin t) (ha : (i,a) ∈ D) :
      π i a = (p (i,a)).2 :=
    (Classical.choose_spec (hLocal i)) a ha
  let q : Equiv.Perm (Fin s × Fin t) :=
    { toFun := fun x => (σ x.1, π x.1 x.2)
      invFun := fun x => (σ.symm x.1, (π (σ.symm x.1)).symm x.2)
      left_inv := by
        intro x
        rcases x with ⟨i,a⟩
        change (σ.symm (σ i),
          (π (σ.symm (σ i))).symm (π i a)) = (i,a)
        simp
      right_inv := by
        intro x
        rcases x with ⟨i,a⟩
        change (σ (σ.symm i),
          π (σ.symm i) ((π (σ.symm i)).symm a)) = (i,a)
        simp }
  have hAut : IsGraphAutomorphism (cliqueUnion s t) q := by
    intro x y
    rcases x with ⟨i,a⟩
    rcases y with ⟨j,b⟩
    change (i = j ∧ a ≠ b) ↔
      (σ i = σ j ∧ π i a ≠ π j b)
    constructor
    · rintro ⟨hij,hab⟩
      subst j
      exact ⟨rfl,(π i).injective.ne hab⟩
    · rintro ⟨hij,hne⟩
      have hIdx : i = j := σ.injective hij
      subst j
      exact ⟨rfl,fun hab => hne (congrArg (π i) hab)⟩
  refine ⟨q,hAut,?_⟩
  intro x hx
  rcases x with ⟨i,a⟩
  apply Prod.ext
  · exact hσCorrect i a hx
  · exact hπCorrect i a hx

end EPPAIII.CliqueCovers
