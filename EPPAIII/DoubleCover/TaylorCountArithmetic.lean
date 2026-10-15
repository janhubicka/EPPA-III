import EPPAIII.DoubleCover.TaylorThreeLayerCount
import EPPAIII.DoubleCover.ClusterNeighbourPartition

namespace EPPAIII.DoubleCover

theorem clusterBaseComponent_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) (x : V) :
    (clusterBaseComponent G x).card =
      (clusterBaseNeighbours G x).card + 1 := by
  classical
  have hx : x ∉ clusterBaseNeighbours G x := by
    simp [clusterBaseNeighbours]
  simpa [clusterBaseComponent] using
    (Finset.card_insert_of_notMem hx)

/-- Normalize the exact finite layer-count arithmetic over integers. -/
theorem taylor_ordered_triangle_count_arithmetic
    (T E d s k t n : ℕ)
    (hTriangle : T = (d * d - d) + 2 * (d * s) + t)
    (hEdges : E = (k * k - k) + t)
    (hComponent : k = d + 1)
    (hPartition : n = d + s + 1) :
    (T : ℤ) = (E : ℤ) +
      2 * (d : ℤ) * ((n : ℤ) - (d : ℤ) - 2) := by
  have hd : d ≤ d * d := by
    cases d with
    | zero => simp
    | succ d => nlinarith
  have hk : k ≤ k * k := by
    rw [hComponent]
    nlinarith
  have hTrianglePlus : T + d = d * d + 2 * (d * s) + t := by
    omega
  have hEdgePlus : E + k = k * k + t := by
    omega
  have hTZ :
      (T : ℤ) + (d : ℤ) =
        (d : ℤ) * (d : ℤ) + 2 * (d : ℤ) * (s : ℤ) + (t : ℤ) := by
    exact_mod_cast hTrianglePlus
  have hEZ :
      (E : ℤ) + (k : ℤ) =
        (k : ℤ) * (k : ℤ) + (t : ℤ) := by
    exact_mod_cast hEdgePlus
  have hKZ : (k : ℤ) = (d : ℤ) + 1 := by
    exact_mod_cast hComponent
  have hNZ : (n : ℤ) = (d : ℤ) + (s : ℤ) + 1 := by
    exact_mod_cast hPartition
  nlinarith

end EPPAIII.DoubleCover
