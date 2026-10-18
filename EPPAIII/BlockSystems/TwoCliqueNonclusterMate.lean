import EPPAIII.BlockSystems.TwoCliqueActualTaylorNamed
import EPPAIII.BlockSystems.ClusterObstructions

/-!
# Excluding the mate-free model in the unequal-clique case

The actual Taylor pair pattern from Lemma 6.6 has a uniform
optional mate matching. With no matching, the named graph is
a disjoint union of two complete graphs, hence a cluster graph.

Under the non-cluster hypothesis actually used by the Lean
classification, all mates must therefore be adjacent. These
results do not require positivity or unequal sizes of the
two colour classes, and do not use Gardiner's classification.
-/

namespace EPPAIII.BlockSystems

/-- Without mate edges, the two-clique Taylor model is a
disjoint union of complete graphs, hence a cluster graph. -/
theorem twoCliqueMatchedGraph_false_is_cluster
    {V : Type*} (c : V → Bool) :
    IsClusterGraph (twoCliqueMatchedGraph c false) := by
  intro a b d hab hbd had
  change twoCliqueMatchedRel c false a b at hab
  change twoCliqueMatchedRel c false b d at hbd
  change twoCliqueMatchedRel c false a d
  have hab' : Bool.xor a.1 (c a.2) =
      Bool.xor b.1 (c b.2) := by
    rcases hab.2 with h | h
    · exact h
    · cases h.1
  have hbd' : Bool.xor b.1 (c b.2) =
      Bool.xor d.1 (c d.2) := by
    rcases hbd.2 with h | h
    · exact h
    · cases h.1
  exact ⟨had, Or.inl (hab'.trans hbd')⟩

/-- A non-cluster Taylor host cannot be the mate-free model. -/
theorem twoClique_matched_noncluster_forces_mate
    {V : Type*} (c : V → Bool)
    (H : SimpleGraph (Bool × V)) (mate : Bool)
    (hEq : H = twoCliqueMatchedGraph c mate)
    (hNonCluster : ¬ IsClusterGraph H) :
    mate = true := by
  cases mate with
  | false =>
      exfalso
      apply hNonCluster
      rw [hEq]
      exact twoCliqueMatchedGraph_false_is_cluster c
  | true => rfl

/-- Under the actual non-cluster hypothesis, the final named host
is precisely two complete graphs joined by the full mate matching. -/
theorem twoClique_actual_taylor_noncluster_is_matched
    {V : Type*} (c : V → Bool)
    (H : SimpleGraph (Bool × V)) (mate : Bool)
    (hBottom : ∀ x y : V,
      H.Adj (false,x) (false,y) ↔
        (twoCliqueGraph c).Adj x y)
    (hPattern : DoubleCover.RepresentsPairPattern
      (twoCliqueGraph c) H DoubleCover.taylor)
    (hMate : ∀ x : V,
      H.Adj (false,x) (true,x) ↔ mate = true)
    (hNonCluster : ¬ IsClusterGraph H) :
    H = twoCliqueMatchedGraph c true := by
  have hEq : H = twoCliqueMatchedGraph c mate :=
    twoClique_actual_taylor_is_matched c H mate
      hBottom hPattern hMate
  have hm : mate = true :=
    twoClique_matched_noncluster_forces_mate
      c H mate hEq hNonCluster
  simpa only [hm] using hEq

end EPPAIII.BlockSystems
