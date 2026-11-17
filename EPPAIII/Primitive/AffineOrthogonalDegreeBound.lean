import EPPAIII.Primitive.BinaryOrthogonalTransport
import EPPAIII.Primitive.FiniteExclusions

/-!
# Degree restriction for a selected half of an affine binary model

The bound only needs the two certified constituent maxima for the
given sign and the exact order of the selected graph.
-/

namespace EPPAIII.Primitive

/-- At every selected vertex of an order-32 EPPA base, the selected degree
lies between 15 and 16 if both point constituents have EPPA base order at
most 16. -/
theorem affineOrthogonal_degreeBound {V : Type*} [Finite V] (plus : Bool)
    (hSing : maxEppaOrder (orthogonalSixGraph plus true) ≤ 16)
    (hNonsing : maxEppaOrder (orthogonalSixGraph plus false) ≤ 16)
    (G : SimpleGraph V) (e : V ↪ Fin 64)
    (he : IsEPPAEmbedding G (vectorOrthogonalSixGraph plus) e)
    (hCard : Nat.card V = 32) (v : V) :
    15 ≤ Nat.card (G.neighborSet v) ∧ Nat.card (G.neighborSet v) ≤ 16 := by
  let H := vectorOrthogonalSixGraph plus
  have hLocal := order_le_maxEppaOrder _ _ _ (local_eppa G H e he v)
  have hNonlocal := order_le_maxEppaOrder _ _ _ (nonlocal_eppa G H e he v)
  have hLocalModel := maxEppaOrder_le_of_iso (affineOrthogonalLocalIso plus (e v))
  have hNonlocalModel := maxEppaOrder_le_of_iso (affineOrthogonalNonlocalIso plus (e v))
  have hSplit := order_eq_one_add_subconstituent_orders G v
  change Nat.card (G.neighborSet v) ≤ maxEppaOrder (localGraph H (e v)) at hLocal
  change Nat.card {x : V // v ≠ x ∧ ¬ G.Adj v x} ≤
    maxEppaOrder (nonlocalGraph H (e v)) at hNonlocal
  dsimp only [H] at hLocal hNonlocal
  omega

end EPPAIII.Primitive
