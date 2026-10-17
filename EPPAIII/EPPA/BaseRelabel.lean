import EPPAIII.EPPA.Definitions

/-!
# Relabelling the selected base of a fixed EPPA embedding

The new embedding is obtained by precomposing the old embedding with
an equivalence of finite base vertex sets. Partial automorphisms
are conjugated through that equivalence; no coherent choice of
extensions is needed.
-/

namespace EPPAIII

def relabelEmbedding {U V W : Type*}
    (e : V ↪ W) (φ : U ≃ V) : U ↪ W where
  toFun := fun u => e (φ u)
  inj' := by
    intro u v h
    exact φ.injective (e.injective h)

/-- Transport the complete EPPA property through a base relabelling,
while leaving the ambient witness and its vertices unchanged. -/
theorem eppa_relabel_base {U V W : Type*}
    [Fintype U] [Fintype V]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (heppa : IsEPPAEmbedding G H e)
    (φ : U ≃ V) (G' : SimpleGraph U)
    (hModel : ∀ a b : U, G'.Adj a b ↔ G.Adj (φ a) (φ b)) :
    IsEPPAEmbedding G' H (relabelEmbedding e φ) := by
  classical
  constructor
  · intro a b
    exact (hModel a b).trans (heppa.1 (φ a) (φ b))
  · intro D p hp
    let q : Equiv.Perm V := (φ.symm.trans p).trans φ
    let E : Finset V := D.image φ
    have hinv (v : V) (hv : v ∈ E) : φ.symm v ∈ D := by
      obtain ⟨u,hu,huv⟩ := Finset.mem_image.mp hv
      simpa [←huv] using hu
    have hPart : IsPartialGraphAutomorphism G E q := by
      intro a b ha hb
      have ha' := hinv a ha
      have hb' := hinv b hb
      calc
        G.Adj a b ↔ G'.Adj (φ.symm a) (φ.symm b) := by
          simpa using (hModel (φ.symm a) (φ.symm b)).symm
        _ ↔ G'.Adj (p (φ.symm a)) (p (φ.symm b)) :=
          hp (φ.symm a) (φ.symm b) ha' hb'
        _ ↔ G.Adj (q a) (q b) := by
          simpa [q] using (hModel
            (p (φ.symm a)) (p (φ.symm b)))
    obtain ⟨Q,hQ,hRestrict⟩ := heppa.2 E q hPart
    refine ⟨Q,hQ,?_⟩
    intro a ha
    change Q (e (φ a)) = e (φ (p a))
    have haE : φ a ∈ E :=
      Finset.mem_image.mpr ⟨a,ha,rfl⟩
    simpa [q] using hRestrict (φ a) haE

end EPPAIII
