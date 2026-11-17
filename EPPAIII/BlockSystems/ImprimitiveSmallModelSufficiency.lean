import EPPAIII.BlockSystems.CycleFiveSmallCrossConclusion
import EPPAIII.BlockSystems.RookThreeFinalImprimitiveClassification
import EPPAIII.BlockSystems.DisjointDoubleNonhomogeneity
import EPPAIII.Primitive.AffineLineCompletion
import EPPAIII.EPPA.HostRelabel
import Mathlib.Tactic.FinCases

/-! # Sufficiency for the actual exceptional homogeneous double models -/

namespace EPPAIII.BlockSystems

open SimpleGraph DoubleCover

private theorem eppa_of_lower_lifts {V : Type*} (G : SimpleGraph V)
    (H : SimpleGraph (Bool × V)) (hHom : IsHomogeneousGraph G)
    (hBottom : ∀ x y, G.Adj x y ↔ H.Adj (false, x) (false, y))
    (hLift : ∀ q : Equiv.Perm V, IsGraphAutomorphism G q →
      ∃ r : Equiv.Perm (Bool × V), IsGraphAutomorphism H r ∧
        ∀ x, r (false, x) = (false, q x)) :
    IsEPPAEmbedding G H (bottomEmbedding V) := by
  refine ⟨hBottom, ?_⟩
  intro D p hp
  obtain ⟨q, hq, hAgree⟩ := hHom D p hp
  obtain ⟨r, hr, hLower⟩ := hLift q hq
  exact ⟨r, hr, fun x hx => by
    change r (false, x) = (false, p x)
    rw [hLower x, hAgree x hx]⟩

private theorem fromRel_automorphism {U : Type*} (R : U → U → Prop)
    (q : Equiv.Perm U) (hR : ∀ u v, R u v ↔ R (q u) (q v)) :
    IsGraphAutomorphism (fromRel R) q := by
  intro u v
  change (u ≠ v ∧ (R u v ∨ R v u)) ↔
    (q u ≠ q v ∧ (R (q u) (q v) ∨ R (q v) (q u)))
  simp only [ne_eq, q.injective.eq_iff, ← hR]

/-- Relabel a canonical double along a host isomorphism that carries its lower
embedding to the specified embedding. -/
theorem eppa_of_lower_model {U W : Type*} (G : SimpleGraph U)
    (H : SimpleGraph W) (e : U ↪ W) (K : SimpleGraph (Bool × U))
    (φ : Bool × U ≃ W) (hLower : ∀ x, φ (false, x) = e x)
    (hGraph : H.comap φ = K)
    (heppa : IsEPPAEmbedding G K (bottomEmbedding U)) :
    IsEPPAEmbedding G H e := by
  let hPhi : K ≃g H := ⟨φ, by intro x y; rw [← hGraph]; rfl⟩
  have hTransport := eppa_relabel_host G (bottomEmbedding U) heppa hPhi
  have hEmb : (bottomEmbedding U).trans hPhi.toEquiv.toEmbedding = e := by
    ext x
    exact hLower x
  simpa only [hEmb] using hTransport

private theorem rookThree_homogeneous' : IsHomogeneousGraph rookThreeGraph :=
  Primitive.rookThree_homogeneous

/-- The simultaneous coordinate action preserves the corresponding mate
matching, including when the second layer has complementary adjacency. -/
theorem rookMatchingGraph_eppa (topComplement : Bool) :
    IsEPPAEmbedding rookThreeGraph (rookMatchingGraph topComplement)
      (bottomEmbedding rookVertex) := by
  apply eppa_of_lower_lifts _ _ rookThree_homogeneous'
  · intro x y
    rw [rookMatchingGraph_adj_iff]
    simp [rookMatchingRelation]
  · intro q hq
    let r := Equiv.prodCongr (Equiv.refl Bool) q
    refine ⟨r, fromRel_automorphism _ r ?_, fun _ => rfl⟩
    rintro ⟨i,x⟩ ⟨j,y⟩
    change rookMatchingRelation topComplement (i, x) (j, y) ↔
      rookMatchingRelation topComplement (i, q x) (j, q y)
    simp only [rookMatchingRelation,
      ne_eq, q.injective.eq_iff, ← hq x y]

/-- Both named rook degree-four cross relations are preserved by
the simultaneous coordinate action. -/
theorem rookDoubleGraph_eppa (crossNonrook : Bool) :
    IsEPPAEmbedding rookThreeGraph (rookDoubleGraph false crossNonrook)
      (bottomEmbedding rookVertex) := by
  apply eppa_of_lower_lifts _ _ rookThree_homogeneous'
  · intro x y
    change rookThreeGraph.Adj x y ↔ ((false, x) ≠ (false, y) ∧
      (rookDoubleRelation false crossNonrook (false, x) (false, y) ∨
        rookDoubleRelation false crossNonrook (false, y) (false, x)))
    constructor
    · intro h
      exact ⟨fun hEq => rookThreeGraph.ne_of_adj h (congrArg Prod.snd hEq), Or.inl h⟩
    · rintro ⟨_, h | h⟩
      · exact h
      · exact h.symm
  · intro q hq
    let r := Equiv.prodCongr (Equiv.refl Bool) q
    refine ⟨r, fromRel_automorphism _ r ?_, fun _ => rfl⟩
    rintro ⟨i,x⟩ ⟨j,y⟩
    change rookDoubleRelation false crossNonrook (i, x) (j, y) ↔
      rookDoubleRelation false crossNonrook (i, q x) (j, q y)
    simp only [rookDoubleRelation,
      ne_eq, q.injective.eq_iff, ← hq x y]

/-- The actual selected rook embedding in any named small host suffices for EPPA. -/
theorem RookSmallHostPatterns.eppa {W : Type*} [Fintype W]
    {H : SimpleGraph W} {e : rookVertex ↪ W} (h : RookSmallHostPatterns H e) :
    IsEPPAEmbedding rookThreeGraph H e := by
  rcases h with ⟨φ, hLower, hGraph⟩ |
      ⟨φ, c, hLower, hGraph⟩ | ⟨φ, c, hLower, hGraph⟩
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph
      (disjoint_double_eppa_of_homogeneous rookThreeGraph rookThree_homogeneous')
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph (rookMatchingGraph_eppa c)
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph (rookDoubleGraph_eppa c)

private theorem c5_explicit_automorphism (q : Equiv.Perm (Fin 5))
    (hq : IsGraphAutomorphism (cycleGraph 5) q) (x y : Fin 5) :
    cycleFiveExplicitAdjacent x y ↔ cycleFiveExplicitAdjacent (q x) (q y) :=
  (cycleFiveExplicitAdjacent_iff x y).trans <|
    (hq x y).trans (cycleFiveExplicitAdjacent_iff (q x) (q y)).symm

/-- The simultaneous cyclic action preserves each named matching graph. -/
theorem cycleFiveMatchingGraph_eppa (topComplement : Bool) :
    IsEPPAEmbedding (cycleGraph 5) (cycleFiveMatchingGraph topComplement)
      (bottomEmbedding (Fin 5)) := by
  apply eppa_of_lower_lifts _ _ Primitive.cycleFive_homogeneous
  · intro x y
    rw [cycleFiveMatchingGraph_adj_iff]
    simpa only [cycleFiveMatchingRelation, ite_true] using
      (cycleFiveExplicitAdjacent_iff x y).symm
  · intro q hq
    let r := Equiv.prodCongr (Equiv.refl Bool) q
    refine ⟨r, fromRel_automorphism _ r ?_, fun _ => rfl⟩
    rintro ⟨i,x⟩ ⟨j,y⟩
    change cycleFiveMatchingRelation topComplement (i, x) (j, y) ↔
      cycleFiveMatchingRelation topComplement (i, q x) (j, q y)
    simp only [cycleFiveMatchingRelation,
      ne_eq, q.injective.eq_iff, ← c5_explicit_automorphism q hq x y]

private def c5Reflection (a : Fin 5) : Equiv.Perm (Fin 5) :=
  ⟨fun x => a - x, fun x => a - x, (by decide : ∀ a x : Fin 5, a - (a - x) = x) a,
    (by decide : ∀ a x : Fin 5, a - (a - x) = x) a⟩

private def c5Symmetry (a : Fin 5) (reflect : Bool) : Equiv.Perm (Fin 5) :=
  if reflect then c5Reflection a else Equiv.addRight a

private theorem c5Symmetry_auto :
    ∀ a : Fin 5, ∀ reflect : Bool, ∀ u v : Fin 5,
      (cycleGraph 5).Adj u v ↔ (cycleGraph 5).Adj (c5Symmetry a reflect u) (c5Symmetry a reflect v) := by
  decide

private theorem c5Symmetry_apply_zero :
    ∀ a : Fin 5, ∀ reflect : Bool, c5Symmetry a reflect 0 = a := by decide

private theorem c5Symmetry_apply_one :
    ∀ a : Fin 5, ∀ reflect : Bool, c5Symmetry a reflect 1 = if reflect then a - 1 else a + 1 := by decide

private theorem c5_adj_iff :
    ∀ a b : Fin 5, (cycleGraph 5).Adj a b ↔ b = a + 1 ∨ b = a - 1 := by decide

private theorem c5_other_neighbor :
    ∀ a b c d : Fin 5, (cycleGraph 5).Adj a b → (cycleGraph 5).Adj a c →
      (cycleGraph 5).Adj a d → c ≠ b → d ≠ b → c = d := by decide

private theorem c5_auto_fixed01 (q : Equiv.Perm (Fin 5))
    (hq : IsGraphAutomorphism (cycleGraph 5) q) (h0 : q 0 = 0) (h1 : q 1 = 1) :
    q = 1 := by
  have h2 : q 2 = 2 := by
    apply c5_other_neighbor 1 0
    · decide
    · simpa only [h1] using (hq 1 2).mp (by decide)
    · decide
    · rw [← h0]
      exact q.injective.ne (by decide)
    · decide
  have h3 : q 3 = 3 := by
    apply c5_other_neighbor 2 1
    · decide
    · simpa only [h2] using (hq 2 3).mp (by decide)
    · decide
    · rw [← h1]
      exact q.injective.ne (by decide)
    · decide
  have h4 : q 4 = 4 := by
    apply c5_other_neighbor 3 2
    · decide
    · simpa only [h3] using (hq 3 4).mp (by decide)
    · decide
    · rw [← h2]
      exact q.injective.ne (by decide)
    · decide
  apply Equiv.ext
  intro x
  fin_cases x <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

private theorem c5_auto_symmetry (q : Equiv.Perm (Fin 5))
    (hq : IsGraphAutomorphism (cycleGraph 5) q) :
    ∃ a reflect, q = c5Symmetry a reflect := by
  have hBuild (r : Equiv.Perm (Fin 5)) (hr : IsGraphAutomorphism (cycleGraph 5) r)
      (h0 : r 0 = q 0) (h1 : r 1 = q 1) : q = r := by
    have hq' : IsGraphAutomorphism (cycleGraph 5) (q.trans r.symm) := by
      intro x y
      exact (hq x y).trans <| by
        simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using
          (hr (r.symm (q x)) (r.symm (q y))).symm
    have hEq := c5_auto_fixed01 (q.trans r.symm) hq'
      (by simp [← h0]) (by simp [← h1])
    apply Equiv.ext
    intro x
    have hx : r.symm (q x) = x :=
      congrArg (fun f : Equiv.Perm (Fin 5) => f x) hEq
    exact r.symm.injective (hx.trans (r.symm_apply_apply x).symm)
  rcases (c5_adj_iff (q 0) (q 1)).mp ((hq 0 1).mp (by decide)) with h | h
  · refine ⟨q 0, false, hBuild _ (c5Symmetry_auto _ _) (c5Symmetry_apply_zero _ _) ?_⟩
    simpa only [c5Symmetry_apply_one, Bool.false_eq_true, ite_false] using h.symm
  · refine ⟨q 0, true, hBuild _ (c5Symmetry_auto _ _) (c5Symmetry_apply_zero _ _) ?_⟩
    simpa only [c5Symmetry_apply_one, ite_true] using h.symm

private def c5DoubleLift (diagonal : Bool) (a : Fin 5) (reflect : Bool) :
    Equiv.Perm (Bool × Fin 5) :=
  let layers := Equiv.sigmaCongrRight (β₁ := fun _ => Fin 5) (β₂ := fun _ => Fin 5)
    (fun side => c5Symmetry (if side && reflect then a - (if diagonal then 2 else 1) else a) reflect)
  let code := Equiv.sigmaEquivProd Bool (Fin 5)
  (code.symm.trans layers).trans code

set_option maxHeartbeats 2000000 in
private theorem c5DoubleLift_relation :
    ∀ diagonal : Bool, ∀ a : Fin 5, ∀ reflect : Bool, ∀ u v : Bool × Fin 5,
      cycleFiveDoubleRelation false diagonal u v ↔
        cycleFiveDoubleRelation false diagonal (c5DoubleLift diagonal a reflect u)
          (c5DoubleLift diagonal a reflect v) := by
  decide

private theorem c5DoubleLift_bottom :
    ∀ diagonal : Bool, ∀ a : Fin 5, ∀ reflect : Bool, ∀ x : Fin 5,
      c5DoubleLift diagonal a reflect (false, x) = (false, c5Symmetry a reflect x) := by
  decide

/-- A lower reflection induces the appropriate shift on each upper
pair profile, preserving both the cross edges and upper cyclic adjacency. -/
theorem cycleFiveDoubleGraph_eppa (diagonal : Bool) :
    IsEPPAEmbedding (cycleGraph 5) (cycleFiveDoubleGraph false diagonal)
      (bottomEmbedding (Fin 5)) := by
  apply eppa_of_lower_lifts _ _ Primitive.cycleFive_homogeneous
  · intro x y
    rw [cycleFiveDoubleGraph_adj_iff]
    simpa only [cycleFiveDoubleRelation, ite_true] using (cycleFiveExplicitAdjacent_iff x y).symm
  · intro q hq
    obtain ⟨a, reflect, rfl⟩ := c5_auto_symmetry q hq
    exact ⟨c5DoubleLift diagonal a reflect,
      fromRel_automorphism _ _ (c5DoubleLift_relation diagonal a reflect),
      c5DoubleLift_bottom diagonal a reflect⟩

/-- The actual selected five-cycle embedding in any named small host suffices for EPPA. -/
theorem CycleFiveSmallHostPatterns.eppa {W : Type*} [Fintype W]
    {H : SimpleGraph W} {e : Fin 5 ↪ W} (h : CycleFiveSmallHostPatterns H e) :
    IsEPPAEmbedding (cycleGraph 5) H e := by
  rcases h with ⟨φ, hLower, hGraph⟩ | ⟨φ, hLower, hGraph⟩ | ⟨φ, d, hLower, hGraph⟩
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph
      (disjoint_double_eppa_of_homogeneous (cycleGraph 5) Primitive.cycleFive_homogeneous)
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph (cycleFiveMatchingGraph_eppa false)
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph (cycleFiveDoubleGraph_eppa d)

end EPPAIII.BlockSystems
