import EPPAIII.Primitive.AffineLineExclusion
import EPPAIII.Primitive.RookBounds
import EPPAIII.CliqueCovers.CliqueUnionHomogeneity

/-! # The small endpoints of the affine-line argument -/

namespace EPPAIII.Primitive

open SimpleGraph
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover

private def cycleFiveReflection (x y z : Fin 5) : Fin 5 :=
  x + y - z

private theorem cycleFiveReflection_involutive :
    ∀ x y : Fin 5, ∀ z : Fin 5, cycleFiveReflection x y (cycleFiveReflection x y z) = z := by
  decide

private def cycleFiveMover (x y : Fin 5) : Equiv.Perm (Fin 5) :=
  if x = y then Equiv.refl _ else
    ⟨cycleFiveReflection x y, cycleFiveReflection x y,
      cycleFiveReflection_involutive x y, cycleFiveReflection_involutive x y⟩

private theorem cycleFiveMover_auto :
    ∀ x y : Fin 5, ∀ u v : Fin 5,
      (cycleGraph 5).Adj u v ↔ (cycleGraph 5).Adj (cycleFiveMover x y u) (cycleFiveMover x y v) := by
  decide

private theorem cycleFiveMover_sends :
    ∀ x y : Fin 5, cycleFiveMover x y x = y := by decide

private theorem cycleFiveMover_fixes :
    ∀ x y z : Fin 5, z ≠ x → z ≠ y →
      ((cycleGraph 5).Adj x z ↔ (cycleGraph 5).Adj y z) → cycleFiveMover x y z = z := by
  decide

/-- The five-cycle is homogeneous, by the finite reflections. -/
theorem cycleFive_homogeneous : IsHomogeneousGraph (cycleGraph 5) :=
  homogeneous_of_pair_movers _ cycleFiveMover cycleFiveMover_auto
    cycleFiveMover_sends cycleFiveMover_fixes

private theorem homogeneous_of_model {V W : Type*} [Finite V]
    {G : SimpleGraph V} {H : SimpleGraph W} (hModel : IsModelUpToComplement G H)
    (hHom : IsHomogeneousGraph H) : IsHomogeneousGraph G := by
  rcases hModel with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact homogeneous_graph_of_iso φ hHom
  · exact homogeneous_graph_of_iso φ ((homogeneous_complement_iff _).mp hHom)

/-- Connection parameters and concrete identifications for the finitely
many possible small endpoints. The isomorphisms are graph recognition data. -/
inductive AffineLineConnection {F : Type*} [Field F] [Fintype F]
    (H : SimpleGraph F) (p r : ℕ) : Prop
  | paley (hResidue : Nat.card F % 4 = 1)
      (hFive : Nat.card F = 5 → IsModelUpToComplement H (cycleGraph 5))
      (hNine : Nat.card F = 9 → IsModelUpToComplement H (rookGraph 3))
  | peisert (hResidue : p % 4 = 3) (hEven : r % 2 = 0)
      (hNine : Nat.card F = 9 → IsModelUpToComplement H (rookGraph 3))
  | vanLintSchrijver (ℓ : ℕ) (hOdd : ℓ % 2 = 1) (hLarge : 2 < ℓ)
      (hIndex : ℓ ∣ Nat.card F - 1) (hExtension : ℓ - 1 ∣ r)
      (hFour : Nat.card F = 4 → ℓ = 3 → IsModelUpToComplement H (cliqueUnion 2 2))
      (hSixteenThree : Nat.card F = 16 → ℓ = 3 → IsModelUpToComplement H clebschGraph)
      (hSixteenFive : Nat.card F = 16 → ℓ = 5 → IsModelUpToComplement H (cliqueUnion 4 4))

/-- The affine size bound and the small model identifications take the
selected pair into the classified cases. -/
theorem affineLine_listed_of_eppa {V K F : Type*} [Finite V]
    [Field K] [Field F] [Fintype F] [Algebra K F] [FiniteDimensional K F]
    (G : SimpleGraph V) (H : SimpleGraph F) (e : V ↪ F)
    (hEPPA : IsEPPAEmbedding G H e) (hHalf : Nat.card F ≤ 2 * Nat.card V)
    (hAffine : HasAffineLineAction K H) {p : ℕ} (hp : p.Prime)
    (hCard : Nat.card F = p ^ Module.finrank K F)
    (hConnection : AffineLineConnection H p (Module.finrank K F)) :
    IsListedPrimitiveHost H := by
  have hp₄ : p ≠ 4 := fun h => (by decide : ¬ Nat.Prime 4) (h ▸ hp)
  have hDegree : 0 < Module.finrank K F := Module.finrank_pos
  cases hConnection with
  | paley hResidue hFive hNine =>
      rcases affineLine_paley_host_orders G H e hEPPA hHalf hAffine hp.two_le hp₄ hDegree hCard
        hResidue with h | h
      · exact Or.inl (homogeneous_of_model (hFive h) cycleFive_homogeneous)
      · exact Or.inl (homogeneous_of_model (hNine h) rookThree_homogeneous)
  | peisert hResidue hEven hNine =>
      have h := affineLine_peisert_host_order G H e hEPPA hHalf hAffine hp.two_le hp₄ hDegree
        hCard hResidue hEven
      exact Or.inl (homogeneous_of_model (hNine h) rookThree_homogeneous)
  | vanLintSchrijver ℓ hOdd hLarge hIndex hExtension hFour hThree hFive =>
      rcases affineLine_vanLintSchrijver_host_orders G H e hEPPA hHalf hAffine hp.two_le hp₄ hDegree
        hCard hOdd hLarge hIndex hExtension with ⟨hq, hℓ⟩ | ⟨hq, hℓ | hℓ⟩
      · exact Or.inl (homogeneous_of_model (hFour hq hℓ) (cliqueUnion_isHomogeneous 2 2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hThree hq hℓ))))
      · exact Or.inl (homogeneous_of_model (hFive hq hℓ) (cliqueUnion_isHomogeneous 4 4))

end EPPAIII.Primitive
