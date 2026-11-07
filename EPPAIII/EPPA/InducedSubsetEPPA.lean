import EPPAIII.EPPA.Hereditary

/-!
# EPPA on actual induced vertex subsets of a fixed host

The obstacle-hypergraph construction must refer to the selected
*subset of vertices* of H, not just an isomorphism type. We define
the relevant induced graph and its canonical selected embedding,
then prove downward closure of EPPA and upward closure of failure.

The proof uses only the hereditary EPPA theorem; no assumption about
the host being transitive or a particular graph family is needed.
-/

namespace EPPAIII

/-- The graph induced by a specified finite vertex subset of H. -/
def selectedSubsetGraph {V : Type*}
    (H : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v : V // v ∈ S} :=
  H.comap Subtype.val

/-- The literal selected induced embedding into the host. -/
def selectedSubsetInclusion {V : Type*}
    (S : Finset V) : {v : V // v ∈ S} ↪ V where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- H is an EPPA witness for the actual induced subgraph on S. -/
def IsEPPAOnSubset {V : Type*}
    (H : SimpleGraph V) (S : Finset V) : Prop :=
  IsEPPAEmbedding (selectedSubsetGraph H S) H
    (selectedSubsetInclusion S)

/-- Any subset of a selected EPPA set is itself an EPPA set. -/
theorem eppa_on_subset_downward
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {S T : Finset V}
    (hTS : T ⊆ S) (hS : IsEPPAOnSubset H S) :
    IsEPPAOnSubset H T := by
  classical
  let f : {v : V // v ∈ T} ↪ {v : V // v ∈ S} :=
    { toFun := fun x => ⟨x.1, hTS x.2⟩
      inj' := by
        intro x y h
        have hval : (x.1 : V) = y.1 :=
          congrArg (fun z : {v : V // v ∈ S} => z.1) h
        exact Subtype.ext hval }
  have hInduced : IsInducedGraphEmbedding
      (selectedSubsetGraph H T) (selectedSubsetGraph H S) f := by
    intro x y
    rfl
  have hRestricted :=
    eppa_embedding_of_induced_embedding
      (selectedSubsetGraph H T) (selectedSubsetGraph H S) H
      f (selectedSubsetInclusion S) hInduced hS
  exact hRestricted

/-- Once a selected induced subgraph fails EPPA, every larger
selected induced subgraph of the same H also fails EPPA. -/
theorem non_eppa_on_subset_upward
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {S T : Finset V}
    (hST : S ⊆ T) (hBad : ¬ IsEPPAOnSubset H S) :
    ¬ IsEPPAOnSubset H T := by
  intro hT
  exact hBad (eppa_on_subset_downward H hST hT)

end EPPAIII
