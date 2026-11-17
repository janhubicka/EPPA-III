import EPPAIII.Primitive.AffineOrthogonalDegreeBound
import EPPAIII.Primitive.AffineRootDegreeCertificate

/-!
# Applying the affine root degree certificate

An order-32 selected mask from the rooted product list cannot have EPPA.
The point constituent bounds enter only through the degree restriction.
-/

namespace EPPAIII.Primitive

theorem affineRootMask_not_eppa (plus : Bool)
    (hSing : maxEppaOrder (orthogonalSixGraph plus true) ≤ 16)
    (hNonsing : maxEppaOrder (orthogonalSixGraph plus false) ≤ 16)
    (mask : Nat) (hMask : mask ∈ affineRootMaskProducts plus)
    (hCard : Nat.card (maskVertices 64 mask) = 32) :
    ¬ IsEPPAEmbedding ((vectorOrthogonalSixGraph plus).induce (maskVertices 64 mask))
      (vectorOrthogonalSixGraph plus) (Function.Embedding.subtype (maskVertices 64 mask)) := by
  intro hEppa
  obtain ⟨x, hx, hBad⟩ := affineRootMask_badDegree plus mask hMask
  have hBound := affineOrthogonal_degreeBound plus hSing hNonsing _ _ hEppa hCard ⟨x, hx⟩
  rw [← affineMaskDegree_eq_card] at hBound
  exact hBad.elim (not_lt_of_ge hBound.1) (not_lt_of_ge hBound.2)

end EPPAIII.Primitive
