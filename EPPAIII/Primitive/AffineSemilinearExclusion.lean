import EPPAIII.EPPA.HostRelabel
import EPPAIII.Primitive.AffineSemilinearArithmetic
import EPPAIII.Primitive.NeighbourhoodBound
import EPPAIII.Primitive.SemilinearStabilizer

/-!
# Excluding affine hosts with semilinear root stabilizer

The host hypotheses are transitivity to the origin and containment of the
full origin stabilizer in the semilinear group. The proof applies to the
actual selected copy, even when the anchors only determine its span.
-/

namespace EPPAIII.Primitive

private theorem affineSemilinear_rooted_eppa_bound
    {F K V W : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
    [FiniteDimensional F K] [Fintype V] [Fintype W]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (root : V) (hroot : e root = 0)
    (hHalf : Fintype.card W ≤ 2 * Fintype.card V) (hLarge : 4 < Fintype.card W)
    (hAction : ∀ a : Equiv.Perm W, IsGraphAutomorphism H a → a 0 = 0 →
      ∃ (g : K ≃ₐ[F] K) (f : W →ₛₗ[RingHomClass.toRingHom g] W), ∀ x, a x = f x) :
    let n := Module.finrank K W + Nat.log 2 (Module.finrank F K) + 1
    Fintype.card V ≤ 2 ^ n + n := by
  classical
  dsimp only
  let S : Set W := Set.range e
  have hOrder : Fintype.card W = Fintype.card K ^ Module.finrank K W :=
    Module.card_eq_pow_finrank
  have hDimension : Module.finrank K (Submodule.span K S) ≤ Module.finrank K W :=
    (Submodule.span K S).finrank_le
  rcases proper_subfield_or_semilinear_stabilizer_base (F := F) (K := K) S with
    hSubfield | ⟨U, hSelected, hCount, hBase⟩
  · obtain ⟨_, _, _, _, _, _, _, hSquare⟩ := hSubfield
    have hCard : Nat.card S = Fintype.card V :=
      (Nat.card_congr (Equiv.ofInjective e e.injective).symm).trans Nat.card_eq_fintype_card
    rw [hCard] at hSquare
    have hSmall : Fintype.card V ^ 2 ≤ Fintype.card W := by
      rw [hOrder]
      exact hSquare.trans (Nat.pow_le_pow_right (by positivity) hDimension)
    have hSq : Fintype.card W ^ 2 ≤ 4 * Fintype.card W := calc
      Fintype.card W ^ 2 ≤ (2 * Fintype.card V) ^ 2 := Nat.pow_le_pow_left hHalf 2
      _ = 4 * Fintype.card V ^ 2 := by rw [mul_pow]; rfl
      _ ≤ 4 * Fintype.card W := Nat.mul_le_mul_left 4 hSmall
    rw [pow_two] at hSq
    have hBigger := Nat.mul_lt_mul_of_pos_right hLarge (by omega : 0 < Fintype.card W)
    exact False.elim ((not_lt_of_ge hSq) hBigger)
  · have hPre (u : U) : ∃ v, e v = (u : W) := hSelected u.property
    choose pre hPre using hPre
    let A : Finset V := insert root (Finset.univ.image pre)
    have hA : A.card ≤ U.card + 1 := by
      change (insert root (Finset.univ.image pre)).card ≤ _
      have hImage : (Finset.univ.image pre).card ≤ U.card := by
        simpa only [Finset.card_univ, Fintype.card_coe] using Finset.card_image_le (f := pre)
      exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hImage)
    have hFix (a : Equiv.Perm W) (ha : IsGraphAutomorphism H a)
        (hAnchors : ∀ u ∈ A, a (e u) = e u) (v : V) : a (e v) = e v := by
      have hZero : a 0 = 0 := by simpa only [hroot] using hAnchors root (Finset.mem_insert_self _ _)
      obtain ⟨g, f, hf⟩ := hAction a ha hZero
      have hFixU (u : W) (hu : u ∈ U) : f u = u := by
        let w : U := ⟨u, hu⟩
        have hw : pre w ∈ A :=
          Finset.mem_insert_of_mem (Finset.mem_image_of_mem pre (Finset.mem_univ w))
        simpa only [hPre w, hf] using hAnchors (pre w) hw
      exact (hf (e v)).trans (hBase g f hFixU (e v) (Submodule.subset_span ⟨v, rfl⟩))
    have hn : A.card ≤ Module.finrank K W + Nat.log 2 (Module.finrank F K) + 1 := by
      omega
    exact (card_le_pow_add_of_pointwise_fixation G H e heppa A hFix).trans
      (Nat.add_le_add (Nat.pow_le_pow_right (by decide) hn) hn)

/-- A semilinear root stabilizer excludes every EPPA embedding of at least half
the vertices in affine dimension at least four over a field of order at least
three. The root can be moved to the origin by a host graph isomorphism. -/
theorem affineSemilinear_no_half_eppa
    {F K V W : Type*} [Field F] [Field K] [Fintype F] [Fintype K] [Algebra F K]
    [FiniteDimensional F K] [Fintype V] [Fintype W]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e) (hHalf : Fintype.card W ≤ 2 * Fintype.card V)
    (hq : 3 ≤ Fintype.card K) (hd : 4 ≤ Module.finrank K W)
    (hOrigin : ∀ x : W, ∃ a : H ≃g H, a x = 0)
    (hAction : ∀ a : Equiv.Perm W, IsGraphAutomorphism H a → a 0 = 0 →
      ∃ (g : K ≃ₐ[F] K) (f : W →ₛₗ[RingHomClass.toRingHom g] W), ∀ x, a x = f x) :
    False := by
  have hOrder : Fintype.card W = Fintype.card K ^ Module.finrank K W :=
    Module.card_eq_pow_finrank
  have hFieldOrder : Fintype.card K = Fintype.card F ^ Module.finrank F K :=
    Module.card_eq_pow_finrank
  have hCutoff := affineSemilinear_twice_profile_lt_order
    (Fintype.card F) (Module.finrank F K) (Module.finrank K W)
    (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance) Module.finrank_pos
    (hFieldOrder ▸ hq : 3 ≤ Fintype.card F ^ Module.finrank F K) hd
  rw [← hFieldOrder, ← hOrder] at hCutoff
  have hLarge : 4 < Fintype.card W := by omega
  have hNonempty : 0 < Fintype.card V := by omega
  obtain ⟨root⟩ := Fintype.card_pos_iff.mp hNonempty
  obtain ⟨a, ha⟩ := hOrigin (e root)
  have hBound := affineSemilinear_rooted_eppa_bound G H (e.trans a.toEquiv.toEmbedding)
    (eppa_relabel_host G e heppa a) root ha hHalf hLarge hAction
  dsimp only at hBound
  omega

end EPPAIII.Primitive
