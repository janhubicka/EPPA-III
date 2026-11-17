import EPPAIII.Primitive.AffineSurvivorExclusions
import EPPAIII.Primitive.LocalReduction
import EPPAIII.Primitive.UnitaryFourTwoCertificates
import EPPAIII.EPPA.HostRelabel

/-! # Exclusion of the order-45 unitary point graph -/

namespace EPPAIII.Primitive

open SimpleGraph

/-- The order-45 unitary point graph has a (32,9) nonlocal constituent.
The only degree-compatible shape is a complemented cover of width eight.
A pair in one of its blocks would exceed the ambient nonedge codegree. -/
theorem unitaryFourTwo_nonlocal_excludes_forms {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (h : H.IsSRGWith 45 12 3 3) (root : W) :
    let K := nonlocalGraph H root
    (∀ s t, IsEmpty (K ≃g cliqueUnion s t)) ∧
    (∀ s t, IsEmpty (K ≃g (cliqueUnion s t)ᶜ)) ∧
    (∀ s t X Y, IsEmpty (K ≃g coverGraph s t X Y)) ∧
    (∀ s t X Y, IsEmpty (K ≃g (coverGraph s t X Y)ᶜ)) := by
  classical
  let f : nonlocalGraph H root ↪g H := ⟨Function.Embedding.subtype _, Iff.rfl⟩
  exact exclude_forms_of_complement_codegree f (m := 16) (t₀ := 8) (μ := 3)
    (constituentGraph_profile H ⟨45, 12, 3, 3⟩ h root true)
    (by decide) (by decide) rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ hxy hnxy => h.of_not_adj hxy hnxy) (Or.inl (by decide))

/-- The seven-vertex rooted obstruction and the nonlocal shape test
exclude the order-45 unitary graph at an actual selected root. The
local bound is the input certified by the explicit Hermitian check. -/
theorem unitaryFourTwo_not_eppa_of_local_bound {V W : Type*} [Finite V] [Fintype W]
    [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel H.Adj]
    (e : V ↪ W) (root : V) (hSRG : H.IsSRGWith 45 12 3 3)
    (hHalf : Nat.card W ≤ 2 * Nat.card V)
    (hLocal : Nat.card (G.neighborSet root) ≤ 6)
    (hShape : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      let K := nonlocalGraph H (e root)
      (∃ s t, Nonempty (K ≃g cliqueUnion s t) ∨ Nonempty (K ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (K ≃g coverGraph s t X Y) ∨
        Nonempty (K ≃g (coverGraph s t X Y)ᶜ))) : False := by
  classical
  have hOrder : Nat.card W = 45 := Nat.card_eq_fintype_card.trans hSRG.card
  have hNonlocal : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} = 32 :=
    (constituentGraph_profile H ⟨45, 12, 3, 3⟩ hSRG (e root) true).1
  have hSplit := order_eq_one_add_subconstituent_orders G root
  obtain ⟨hC, hCC, hG, hCG⟩ := unitaryFourTwo_nonlocal_excludes_forms H hSRG (e root)
  rcases hShape (by omega) with ⟨s, t, φ | φ⟩ | ⟨s, t, X, Y, φ | φ⟩
  · exact (hC s t).false (Classical.choice φ)
  · exact (hCC s t).false (Classical.choice φ)
  · exact (hG s t X Y).false (Classical.choice φ)
  · exact (hCG s t X Y).false (Classical.choice φ)

/-- The finite Hermitian certificate is transferred to an arbitrary
selected root by the host transitivity supplied by rank three. -/
theorem unitaryFourTwo_not_eppa {V : Type*} [Finite V]
    (G : SimpleGraph V) (e : V ↪ Fin 45)
    (hEPPA : IsEPPAEmbedding G UnitaryFourTwo.graph e) (root : V)
    (hTrans : ∀ x y, ∃ q : Equiv.Perm (Fin 45),
      IsGraphAutomorphism UnitaryFourTwo.graph q ∧ q x = y)
    (hHalf : Nat.card (Fin 45) ≤ 2 * Nat.card V)
    (hShape : Nat.card {x : Fin 45 // e root ≠ x ∧ ¬ UnitaryFourTwo.graph.Adj (e root) x} ≤
      2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      let K := nonlocalGraph UnitaryFourTwo.graph (e root)
      (∃ s t, Nonempty (K ≃g cliqueUnion s t) ∨ Nonempty (K ≃g (cliqueUnion s t)ᶜ)) ∨
      (∃ s t X Y, Nonempty (K ≃g coverGraph s t X Y) ∨
        Nonempty (K ≃g (coverGraph s t X Y)ᶜ))) : False := by
  obtain ⟨q,hq,hr⟩ := hTrans (e root) UnitaryFourTwo.root
  let φ : UnitaryFourTwo.graph ≃g UnitaryFourTwo.graph :=
    ⟨q, fun {x y} => (hq x y).symm⟩
  have hLocal := UnitaryFourTwo.local_order_le_six G (e.trans φ.toEquiv.toEmbedding)
    (eppa_relabel_host G e hEPPA φ) root (by exact hr)
  exact unitaryFourTwo_not_eppa_of_local_bound G UnitaryFourTwo.graph e root
    UnitaryFourTwo.graph_isSRG hHalf hLocal hShape

end EPPAIII.Primitive
