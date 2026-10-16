import EPPAIII.CliqueCovers.ArbitraryHostHalfEdges
import EPPAIII.BlockSystems.GraphTransport

/-!
# A perfect matching of invariant pairs gives canonical EPPA coordinates

Let J be an automorphism-invariant perfect matching graph on the
vertices of a host H. If an embedded half e(V) contains no J-edge
and H has exactly twice as many vertices, every matching edge has
one endpoint in the selected half and the other outside.

We construct the uniquely matched complement of each selected
vertex, and prove the resulting pairs are invariant under every
graph automorphism of H. This avoids assigning arbitrary labels to
the second half and avoids choosing coherent EPPA extensions.

The theorem is an interface for the two-complete-block Case 1 of
the current unequal-clique Lemma 6.6, with J the inter-block
cross-edge graph.
-/

namespace EPPAIII.BlockSystems

/-- The other endpoint of the unique J-edge at each vertex. -/
private noncomputable def invariantMate {W : Type*}
    (J : SimpleGraph W)
    (hMatch : ∀ u : W, ∃! v : W, J.Adj u v)
    (u : W) : W :=
  Classical.choose (hMatch u)

/-- A half-size independent transversal to an invariant perfect
matching determines a canonical two-layer host equivalence.
The induced matching pairs form an invariant imprimitivity system
for H. -/
theorem invariant_perfect_matching_yields_pairs
    {V W : Type*} [Fintype V] [Fintype W]
    (H J : SimpleGraph W)
    (e : V ↪ W)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hMatch : ∀ u : W, ∃! v : W, J.Adj u v)
    (hSelected : ∀ x y : V, ¬ J.Adj (e x) (e y))
    (hInvariant : ∀ q : Equiv.Perm W,
      IsGraphAutomorphism H q → IsGraphAutomorphism J q) :
    ∃ φ : Bool × V ≃ W,
      (∀ x : V, φ (false,x) = e x) ∧
      DoubleCover.HasInvariantPairs (pullbackGraph H φ) := by
  classical
  let mate : W → W := invariantMate J hMatch
  have hMate (u : W) : J.Adj u (mate u) :=
    (Classical.choose_spec (hMatch u)).1
  have hMateInv (u : W) : mate (mate u) = u :=
    (Classical.choose_spec (hMatch (mate u))).2 u (hMate u).symm
  have hOut (x : V) : mate (e x) ∈ finiteOutside e := by
    have hNot : mate (e x) ∉ Set.range e := by
      rintro ⟨y,hy⟩
      exact hSelected x y (by
        simpa [hy] using hMate (e x))
    simpa [finiteOutside] using hNot
  let outsideMap : V → {w : W // w ∈ finiteOutside e} :=
    fun x => ⟨mate (e x),hOut x⟩
  have hOutsideInj : Function.Injective outsideMap := by
    intro x y hxy
    apply e.injective
    have hMatched : mate (e x) = mate (e y) :=
      congrArg Subtype.val hxy
    calc
      e x = mate (mate (e x)) := (hMateInv (e x)).symm
      _ = mate (mate (e y)) := by rw [hMatched]
      _ = e y := hMateInv (e y)
  have hOutsideCard :
      Fintype.card V =
        Fintype.card {w : W // w ∈ finiteOutside e} := by
    rw [Fintype.card_coe,finiteOutside_card,hDouble]
    omega
  let outside : V ≃ {w : W // w ∈ finiteOutside e} :=
    Equiv.ofBijective outsideMap
      ((Fintype.bijective_iff_injective_and_card outsideMap).mpr
        ⟨hOutsideInj,hOutsideCard⟩)
  let φ : Bool × V ≃ W :=
    CliqueCovers.balancedHostEquiv e outside
  have hBottom (x : V) : φ (false,x) = e x :=
    CliqueCovers.balancedHostEquiv_false e outside x
  have hTop (x : V) : φ (true,x) = mate (e x) := by
    change (outside x).val = mate (e x)
    rfl
  have hMatchedPair (x : V) :
      J.Adj (φ (false,x)) (φ (true,x)) := by
    rw [hBottom x,hTop x]
    exact hMate (e x)
  have hOnlyMate (u v : Bool × V)
      (hUV : J.Adj (φ u) (φ v)) : u.2 = v.2 := by
    rcases u with ⟨b,x⟩
    cases b with
    | false =>
        have hAdj : J.Adj (e x) (φ v) := by
          simpa only [hBottom x] using hUV
        have hv : φ v = mate (e x) :=
          (Classical.choose_spec (hMatch (e x))).2 (φ v) hAdj
        have hv' : v = (true,x) :=
          φ.injective (hv.trans (hTop x).symm)
        exact (congrArg Prod.snd hv').symm
    | true =>
        have hAdj : J.Adj (mate (e x)) (φ v) := by
          simpa only [hTop x] using hUV
        have hv : φ v = mate (mate (e x)) :=
          (Classical.choose_spec (hMatch (mate (e x)))).2
            (φ v) hAdj
        have hv' : v = (false,x) :=
          φ.injective ((hv.trans (hMateInv (e x))).trans
            (hBottom x).symm)
        exact (congrArg Prod.snd hv').symm
  have hOther (u v : Bool × V)
      (hSame : u.2 = v.2) (hne : u ≠ v) :
      J.Adj (φ u) (φ v) := by
    rcases u with ⟨a,x⟩
    rcases v with ⟨b,y⟩
    change x = y at hSame
    subst y
    cases a <;> cases b
    · exact False.elim (hne rfl)
    · exact hMatchedPair x
    · exact (hMatchedPair x).symm
    · exact False.elim (hne rfl)
  refine ⟨φ,hBottom,?_⟩
  intro q hq
  let Q : Equiv.Perm W := (φ.symm.trans q).trans φ
  have hBack (u : Bool × V) : Q (φ u) = φ (q u) := by
    simp [Q]
  have hQ : IsGraphAutomorphism H Q := by
    intro u v
    have hh := hq (φ.symm u) (φ.symm v)
    change H.Adj (φ (φ.symm u)) (φ (φ.symm v)) ↔
      H.Adj (φ (q (φ.symm u))) (φ (q (φ.symm v))) at hh
    simpa [Q] using hh
  have hQJ : IsGraphAutomorphism J Q :=
    hInvariant Q hQ
  let f : V → V := fun x => (q (false,x)).2
  have hfInj : Function.Injective f := by
    intro x y hxy
    by_cases hEq : x = y
    · exact hEq
    have hDifferent : q (false,x) ≠ q (false,y) := by
      intro hh
      exact hEq (congrArg Prod.snd (q.injective hh))
    have hAfter : J.Adj (φ (q (false,x))) (φ (q (false,y))) :=
      hOther (q (false,x)) (q (false,y)) hxy hDifferent
    have hBefore : J.Adj (φ (false,x)) (φ (false,y)) := by
      apply (hQJ (φ (false,x)) (φ (false,y))).mpr
      simpa only [hBack (false,x),hBack (false,y)] using hAfter
    exact False.elim (hSelected x y (by
      simpa only [hBottom x,hBottom y] using hBefore))
  have hfSurj : Function.Surjective f :=
    Finite.surjective_of_injective hfInj
  let σ : Equiv.Perm V := Equiv.ofBijective f ⟨hfInj,hfSurj⟩
  refine ⟨σ,?_⟩
  intro b x
  cases b with
  | false =>
      rfl
  | true =>
      have hAfter : J.Adj
          (φ (q (false,x))) (φ (q (true,x))) := by
        have hh :=
          (hQJ (φ (false,x)) (φ (true,x))).mp
            (hMatchedPair x)
        simpa only [hBack (false,x),hBack (true,x)] using hh
      exact (hOnlyMate (q (false,x)) (q (true,x)) hAfter).symm

end EPPAIII.BlockSystems
