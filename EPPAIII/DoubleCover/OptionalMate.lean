import EPPAIII.DoubleCover.TaylorClassification

/-!
# Optional mate matching in a Taylor double

Once the inter-fibre Taylor pattern is known, the adjacency inside
each two-point fibre is the only remaining freedom. One-point EPPA,
together with invariance of the fibre system, proves this adjacency
is the same in every fibre. Thus the witness is the Taylor double
with either all or none of its mate edges present.

The theorem is conditional on the invariant fibre system already
obtained in Claim 3.4 of the manuscript. The graph-level proof of
Claim 3.4 is a separate formalization obligation.
-/

namespace EPPAIII.DoubleCover

/-- The mate edges have a common adjacency type under EPPA.
No non-homogeneity assumption is required for this lemma. -/
theorem eppa_mate_uniform {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (x y : V) :
    H.Adj (false,x) (true,x) ↔ H.Adj (false,y) (true,y) := by
  classical
  let p : Equiv.Perm V := Equiv.swap x y
  have hp : IsPartialGraphAutomorphism G ({x} : Finset V) p := by
    intro u v hu hv
    simp only [Finset.mem_singleton] at hu hv
    subst u
    subst v
    simp
  obtain ⟨q,hq,hExt⟩ := heppa.2 ({x} : Finset V) p hp
  have hbot : q (false,x) = (false,y) := by
    have h := hExt x (by simp)
    change q (false,x) = (false,p x) at h
    simpa [p] using h
  obtain ⟨σ,hσ⟩ := hPairs q hq
  have htop := top_image_of_bottom_image q σ hσ x y hbot
  simpa [hbot, htop] using hq (false,x) (true,x)

/-- Full graph-theoretic conclusion of the two-point proof:
the adjacency between distinct fibres has Taylor form, and the
edges between mates are uniformly present or uniformly absent. -/
theorem eppa_taylor_with_optional_mate {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph (Bool × V))
    (heppa : IsEPPAEmbedding G H (bottomEmbedding V))
    (hPairs : HasInvariantPairs H)
    (hNonHomogeneous : ¬ IsHomogeneousGraph G)
    (xe ye xn yn : V)
    (hEdge : G.Adj xe ye)
    (hNonDistinct : xn ≠ yn)
    (hNonedge : ¬ G.Adj xn yn) :
    ∃ mate : Bool,
      (∀ x : V, H.Adj (false,x) (true,x) ↔ mate = true) ∧
      RepresentsPairPattern G H taylor := by
  classical
  have hInter := eppa_taylor_interfibre G H heppa hPairs
    hNonHomogeneous xe ye xn yn hEdge hNonDistinct hNonedge
  let mate : Bool := decide (H.Adj (false,xe) (true,xe))
  refine ⟨mate, ?_, hInter⟩
  intro x
  have hUniform := eppa_mate_uniform G H heppa hPairs x xe
  simpa [mate] using hUniform

end EPPAIII.DoubleCover
