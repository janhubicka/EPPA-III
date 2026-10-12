import EPPAIII.CliqueCovers.OutsideChoiceImage

/-!
# Canonical finite equivalence between outside vertices and profile choices

Saturation does more than count the outside vertices. It provides a
canonical equivalence between the outside half of a double-sized EPPA
witness and the finite type of admissible coordinate choices.  The
forward map is explicitly the neighbourhood-choice extraction.
The inverse needs no coherent choice of extension automorphisms.

This interface is intended for transporting the induced graph on the
outside half to its finite combinatorial indexing type.
-/

namespace EPPAIII.CliqueCovers

/-- A choice is a selected set of coordinate indices and a finite set
at every selected index, subject to the specified cardinalities. -/
abbrev AdmissibleProfileChoice (s t r k : ℕ) :=
  { choice : Σ R : Finset (Fin s),
      ∀ i : Fin s, i ∈ R → Finset (Fin t) //
      choice ∈ profileChoiceSpace s t r k }

/-- A saturated size-k profile orbit canonically identifies all outside
vertices with admissible choices. No outside graph classification is
presupposed. -/
noncomputable def saturatedOutsideChoiceEquiv {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t) :
    {u : W // u ∈ finiteOutside e} ≃
      AdmissibleProfileChoice s t r k := by
  classical
  let f : {u : W // u ∈ finiteOutside e} →
        AdmissibleProfileChoice s t r k :=
    fun u =>
      ⟨extractKChoice (finiteNeighbourhoodProfile H e u.val) k,
        eppa_saturated_outside_choice_mem
          H e heppa hOrder w hw r k hR hSat u.val u.property⟩
  have hInj : Function.Injective f := by
    intro u v h
    apply Subtype.ext
    have hChoice :
        extractKChoice (finiteNeighbourhoodProfile H e u.val) k =
        extractKChoice (finiteNeighbourhoodProfile H e v.val) k :=
      congrArg Subtype.val h
    exact
      (eppa_saturated_outside_choice_injective
        H e heppa hOrder w hw r k hR hSat)
          u.property v.property hChoice
  have hSurj : Function.Surjective f := by
    intro choice
    obtain ⟨u, ⟨huOutside, huChoice⟩, _⟩ :=
      eppa_saturated_choice_existsUnique_outside
        H e heppa hOrder w hw r k hR hSat
        choice.val choice.property
    refine ⟨⟨u, huOutside⟩, ?_⟩
    apply Subtype.ext
    exact huChoice
  exact Equiv.ofBijective f ⟨hInj, hSurj⟩

/-- The canonical equivalence really sends a vertex to its choice,
rather than an arbitrarily selected label. -/
theorem saturatedOutsideChoiceEquiv_apply {s t : ℕ}
    {W : Type*} [Fintype W]
    (H : SimpleGraph W)
    (e : (Fin s × Fin t) ↪ W)
    (heppa : IsEPPAEmbedding (cliqueUnion s t) H e)
    (hOrder : Fintype.card W = 2 * s * t)
    (w : W) (hw : w ∉ Set.range e)
    (r k : ℕ)
    (hR : (kPositions (finiteNeighbourhoodProfile H e w) k).card = r)
    (hSat : Nat.choose s r * (Nat.choose t k)^r = s * t)
    (u : {u : W // u ∈ finiteOutside e}) :
    (saturatedOutsideChoiceEquiv H e heppa hOrder
       w hw r k hR hSat u).val =
      extractKChoice (finiteNeighbourhoodProfile H e u.val) k := by
  rfl

end EPPAIII.CliqueCovers
