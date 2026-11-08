import EPPAIII.DoubleCover.TwoPointAction

/-!
# The elementary invariant-fibre EPPA obstruction

Under an actual EPPA embedding into a graph whose automorphisms
preserve two-point fibres, two selected pairs with the same edge
status must agree on whether their endpoints share a fibre.

Here we isolate the nonedge case as the precise reason why a
complete nonadjacent fibre plus any outside vertex obstructs EPPA
in the corrected EPPA-III obstacle theorem.

No coherent selection of EPPA automorphism extensions is assumed.
No homogeneity, order bound or graph classification is needed.
-/

namespace EPPAIII.DoubleCover

/-- Two consecutive selected nonedges must have the same
within-fibre / between-fibre status in any actual EPPA embedding
into a host with invariant two-point fibres. -/
theorem selected_nonedges_same_fibre_status
    {U V : Type*} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) (H : SimpleGraph (Bool × V))
    (e : U ↪ Bool × V)
    (heppa : EPPAIII.IsEPPAEmbedding G H e)
    (hPairs : HasInvariantPairs H)
    (a b c : U)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hNonAB : ¬ G.Adj a b) (hNonBC : ¬ G.Adj b c) :
    ((e a).2 = (e b).2 ↔ (e b).2 = (e c).2) := by
  classical
  have hStatus : G.Adj a b ↔ G.Adj b c :=
    ⟨fun h => False.elim (hNonAB h),
      fun h => False.elim (hNonBC h)⟩
  obtain ⟨p,hpa,hpb,hPartial⟩ :=
    partial_of_two_maps G a b b c hab hbc hStatus
  obtain ⟨q,hq,hFix⟩ :=
    heppa.2 ({a,b} : Finset U) p hPartial
  have hA : q (e a) = e b := by
    simpa [hpa] using hFix a (by simp)
  have hB : q (e b) = e c := by
    simpa [hpb] using hFix b (by simp)
  obtain ⟨σ,hσ⟩ := hPairs q hq
  have hA2 : σ (e a).2 = (e b).2 := by
    calc
      σ (e a).2 = (q (e a)).2 :=
        (hσ (e a).1 (e a).2).symm
      _ = (e b).2 := congrArg Prod.snd hA
  have hB2 : σ (e b).2 = (e c).2 := by
    calc
      σ (e b).2 = (q (e b)).2 :=
        (hσ (e b).1 (e b).2).symm
      _ = (e c).2 := congrArg Prod.snd hB
  constructor
  · intro h
    calc
      (e b).2 = σ (e a).2 := hA2.symm
      _ = σ (e b).2 := congrArg σ h
      _ = (e c).2 := hB2
  · intro h
    apply σ.injective
    calc
      σ (e a).2 = (e b).2 := hA2
      _ = (e c).2 := h
      _ = σ (e b).2 := hB2.symm

/-- A selected pair that is a whole fibre, and another selected
nonedge crossing that fibre, contradict actual EPPA. This is
the abstract two-point obstruction behind the corrected
double-cover clause, independently of the third edge. -/
theorem selected_mate_and_cross_nonedge_not_eppa
    {U V : Type*} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) (H : SimpleGraph (Bool × V))
    (e : U ↪ Bool × V)
    (hPairs : HasInvariantPairs H)
    (a b c : U)
    (hab : a ≠ b) (hbc : b ≠ c)
    (hNonAB : ¬ G.Adj a b) (hNonBC : ¬ G.Adj b c)
    (hMate : (e a).2 = (e b).2)
    (hCross : (e b).2 ≠ (e c).2) :
    ¬ EPPAIII.IsEPPAEmbedding G H e := by
  intro hEPPA
  have hStatus :=
    selected_nonedges_same_fibre_status
      G H e hEPPA hPairs a b c hab hbc hNonAB hNonBC
  exact hCross (hStatus.mp hMate)

end EPPAIII.DoubleCover
