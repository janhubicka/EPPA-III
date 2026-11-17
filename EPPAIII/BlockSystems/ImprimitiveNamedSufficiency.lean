import EPPAIII.BlockSystems.ImprimitiveProposition617
import EPPAIII.BlockSystems.ImprimitiveSmallModelSufficiency
import EPPAIII.CliqueCovers.CoverAutomorphismLift
import EPPAIII.CliqueCovers.WagnerSufficiency

/-! # Sufficiency for the named fixed-embedding cases in Proposition 6.17 -/

namespace EPPAIII.BlockSystems

open SimpleGraph DoubleCover

private theorem xor_twice (a b : Bool) : Bool.xor (Bool.xor a b) b = a := by
  cases a <;> cases b <;> rfl

private def xorPerm (d : Bool) : Equiv.Perm Bool :=
  ⟨fun b => Bool.xor b d, fun b => Bool.xor b d, fun b => xor_twice b d, fun b => xor_twice b d⟩

private def cliqueSideEncoding {V : Type*} (c : V → Bool) : Equiv.Perm (Bool × V) :=
  ⟨fun z => (Bool.xor z.1 (c z.2), z.2), fun z => (Bool.xor z.1 (c z.2), z.2),
    fun ⟨b, x⟩ => Prod.ext (xor_twice b (c x)) rfl,
    fun ⟨b, x⟩ => Prod.ext (xor_twice b (c x)) rfl⟩

private theorem colour_from_anchor :
    ∀ a b x y : Bool, (a = x ↔ b = y) → y = Bool.xor x (Bool.xor a b) := by decide

/-- In the double of a two-clique base, a partial map either preserves the
chosen host-side colours on its domain or swaps both colours. Any
permutation extending the selected coordinate map then lifts to the host. -/
theorem twoCliqueMatchedGraph_eppa {V : Type*} (c : V → Bool) (mate : Bool) :
    IsEPPAEmbedding (twoCliqueGraph c) (twoCliqueMatchedGraph c mate) (bottomEmbedding V) := by
  classical
  constructor
  · intro x y
    change (x ≠ y ∧ c x = c y) ↔
      ((false, x) ≠ (false, y) ∧
        (Bool.xor false (c x) = Bool.xor false (c y) ∨ mate = true ∧ x = y))
    simp [ne_eq]
    tauto
  · intro D p hp
    by_cases hEmpty : D = ∅
    · exact ⟨1, fun _ _ => Iff.rfl, by simp [hEmpty]⟩
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    let d := Bool.xor (c a) (c (p a))
    have hColour (x : V) (hx : x ∈ D) : c (p x) = Bool.xor (c x) d := by
      apply colour_from_anchor (c a) (c (p a)) (c x) (c (p x))
      by_cases hax : a = x
      · subst x
        simp
      · have h := hp a x ha hx
        change (a ≠ x ∧ c a = c x) ↔ (p a ≠ p x ∧ c (p a) = c (p x)) at h
        constructor
        · intro hEq
          exact (h.mp ⟨hax, hEq⟩).2
        · intro hEq
          exact (h.mpr ⟨p.injective.ne hax, hEq⟩).2
    let C := cliqueSideEncoding c
    let r := C.trans ((Equiv.prodCongr (xorPerm d) p).trans C)
    have hSide (z : Bool × V) :
        Bool.xor (r z).1 (c (r z).2) = xorPerm d (Bool.xor z.1 (c z.2)) := by
      change Bool.xor (Bool.xor (Bool.xor (Bool.xor z.1 (c z.2)) d) (c (p z.2)))
        (c (p z.2)) = Bool.xor (Bool.xor z.1 (c z.2)) d
      exact xor_twice _ _
    have hIndex (z : Bool × V) : (r z).2 = p z.2 := rfl
    have hr : IsGraphAutomorphism (twoCliqueMatchedGraph c mate) r := by
      intro x y
      change twoCliqueMatchedRel c mate x y ↔ twoCliqueMatchedRel c mate (r x) (r y)
      unfold twoCliqueMatchedRel
      rw [hSide x, hSide y]
      simp only [ne_eq, r.injective.eq_iff, hIndex, (xorPerm d).injective.eq_iff,
        p.injective.eq_iff]
    refine ⟨r, hr, fun x hx => ?_⟩
    change r (false, x) = (false, p x)
    apply Prod.ext
    · change Bool.xor (Bool.xor (Bool.xor false (c x)) d) (c (p x)) = false
      rw [hColour x hx, Bool.false_xor, Bool.xor_self]
    · exact hIndex (false, x)

/-- Every allowed cover or Wagner model extends the selected equal-clique base. -/
theorem EqualCliqueHostModels.eppa {W : Type*} {s t : ℕ}
    {H : SimpleGraph W} {e : (Fin s × Fin t) ↪ W} (h : EqualCliqueHostModels s t H e) :
    IsEPPAEmbedding (cliqueUnion s t) H e := by
  rcases h with ⟨φ, X, Y, hLower, hGraph⟩ | ⟨hs, ht, φ, hLower, hGraph⟩
  · exact eppa_of_lower_model _ _ _ _ φ hLower hGraph
      (CliqueCovers.uniform_cover_isEPPA s t X Y)
  · subst s
    subst t
    exact eppa_of_lower_model _ _ _ _ φ (by simpa using hLower) hGraph
      CliqueCovers.wagnerCanonicalGraph_isEPPA

private theorem eppa_unrelabel_base {U V W : Type*} [Fintype U] [Fintype V]
    (K : SimpleGraph U) (G : SimpleGraph V) {H : SimpleGraph W} {e : V ↪ W}
    (φ : U ≃ V) (hCopy : CanonicalBaseCopy K G φ)
    (h : IsEPPAEmbedding K H (relabelEmbedding e φ)) : IsEPPAEmbedding G H e := by
  have hBack := eppa_relabel_base K H (relabelEmbedding e φ) h φ.symm G
    (fun x y => by simpa using (hCopy (φ.symm x) (φ.symm y)).symm)
  have hEmb : relabelEmbedding (relabelEmbedding e φ) φ.symm = e := by
    ext x
    change e (φ (φ.symm x)) = e x
    rw [φ.apply_symm_apply]
  simpa only [hEmb] using hBack

private theorem eppa_uncomplement_reindexed {V W : Type*} [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) (φ : Equiv.Perm V)
    (hCopy : Gᶜ.comap φ = G) (h : IsEPPAEmbedding G Hᶜ (relabelEmbedding e φ)) :
    IsEPPAEmbedding G H e := by
  have h' : IsEPPAEmbedding Gᶜ Hᶜ e :=
    eppa_unrelabel_base G Gᶜ φ (fun x y => by
      change G.Adj x y ↔ (Gᶜ.comap φ).Adj x y
      rw [hCopy]) h
  simpa only [compl_compl] using eppa_embedding_complement Gᶜ Hᶜ e h'

/-- Each named Proposition 6.17 model witnesses EPPA for its actual selected
embedding, including the alternatives expressed in the opposite orientation. -/
theorem ImprimitiveHostModels.eppa {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : ImprimitiveHostModels G H e) : IsEPPAEmbedding G H e := by
  rcases h with ⟨s,t,_,_,φ,hBase,hModel⟩ | ⟨s,t,_,_,φ,hBase,hModel⟩ |
    ⟨φ,hBase,hModel⟩ | ⟨φ,hBase,hModel⟩ | ⟨c,φ,hBase,hLower,hModel⟩
  · exact eppa_unrelabel_base (cliqueUnion s t) G φ hBase hModel.eppa
  · have hEPPA := eppa_embedding_complement (cliqueUnion s t) Hᶜ _ hModel.eppa
    exact eppa_unrelabel_base (cliqueUnion s t)ᶜ G φ hBase
      (by simpa only [compl_compl] using hEPPA)
  · apply eppa_unrelabel_base (cycleGraph 5) G φ hBase
    rcases hModel with hModel | hModel
    · exact hModel.eppa
    · exact eppa_uncomplement_reindexed _ _ _ _ cycleFiveComplementIndex_comap_back hModel.eppa
  · apply eppa_unrelabel_base rookThreeGraph G φ hBase
    rcases hModel with hModel | hModel
    · exact hModel.eppa
    · exact eppa_uncomplement_reindexed _ _ _ _ rookComplementIndex_comap_back hModel.eppa
  · subst G
    exact eppa_of_lower_model _ _ _ _ φ hLower hModel (twoCliqueMatchedGraph_eppa c true)

end EPPAIII.BlockSystems
