import EPPAIII.CliqueCovers.Basic
import EPPAIII.CliqueCovers.CliqueUnionDegrees

/-!
# Degree and uniform mask size in an all-or-nothing clique cover

Given s outside K_t's with complete-or-empty connections to the s
selected K_t's, the entire cross-adjacency is specified by one
subset mask(j) of the selected clique indices for every outside
clique j.

The labelled graph below has no edges except the two internal sK_t
graphs and these complete cross-blocks. Every right vertex in class
j has degree (t-1) + t*|mask(j)|. Consequently regularity, and hence
vertex-transitivity, forces all outside mask sizes to be equal.

This is the missing numerical input to the EPPA orbit/mask normal
form argument in the zero-partial case of Lemma 3.7. The application
to an actual EPPA witness requires the already verified true-twin
quotient labelling, but that is not a hypothesis hidden here.
-/

namespace EPPAIII.CliqueCovers

/-- Graph on two sK_t halves with complete/empty cross-blocks
specified by a possibly nonuniform outside-index mask family. -/
def maskCoverAdj {s t : ℕ}
    (mask : Fin s → Finset (Fin s))
    (x y : CoverVertex s t) : Prop :=
  (x.1 = y.1 ∧ x.2.1 = y.2.1 ∧ x.2.2 ≠ y.2.2) ∨
  (x.1 = false ∧ y.1 = true ∧ x.2.1 ∈ mask y.2.1) ∨
  (x.1 = true ∧ y.1 = false ∧ y.2.1 ∈ mask x.2.1)

/-- The mask model is a simple graph, with symmetry of cross edges
built in rather than inferred from any matrix normal form. -/
def maskCoverGraph (s t : ℕ)
    (mask : Fin s → Finset (Fin s)) :
    SimpleGraph (CoverVertex s t) where
  Adj := maskCoverAdj mask
  symm := by
    constructor
    intro x y h
    rcases h with ⟨hs,hi,ha⟩ | ⟨hf,ht,hMask⟩ | ⟨ht,hf,hMask⟩
    · exact Or.inl ⟨hs.symm,hi.symm,ha.symm⟩
    · exact Or.inr (Or.inr ⟨ht,hf,hMask⟩)
    · exact Or.inr (Or.inl ⟨hf,ht,hMask⟩)
  loopless := by
    constructor
    intro x h
    rcases h with ⟨_,_,hne⟩ | ⟨hf,ht,_⟩ | ⟨ht,hf,_⟩
    · exact hne rfl
    · exact Bool.false_ne_true (hf.symm.trans ht)
    · exact Bool.false_ne_true (hf.symm.trans ht)

/-- Every outside vertex in clique j has t−1 internal neighbours
and exactly t neighbours per selected base clique in mask(j). -/
theorem maskCoverGraph_right_degree {s t : ℕ}
    (mask : Fin s → Finset (Fin s))
    (j : Fin s) (a : Fin t) :
    (maskCoverGraph s t mask).degree (true,(j,a)) =
      (t - 1) + t * (mask j).card := by
  classical
  let T : Finset (CoverVertex s t) :=
    ({true} : Finset Bool) ×ˢ
      (({j} : Finset (Fin s)) ×ˢ
        ((Finset.univ : Finset (Fin t)).erase a))
  let F : Finset (CoverVertex s t) :=
    ({false} : Finset Bool) ×ˢ
      ((mask j) ×ˢ (Finset.univ : Finset (Fin t)))
  have hNeighbors :
      (maskCoverGraph s t mask).neighborFinset (true,(j,a)) = T ∪ F := by
    ext z
    rcases z with ⟨side,⟨i,b⟩⟩
    cases side <;>
      simp [T,F,maskCoverGraph,maskCoverAdj,
        SimpleGraph.mem_neighborFinset,Finset.mem_product,
        Finset.mem_union,Finset.mem_erase,eq_comm,ne_comm]
  have hDisjoint : Disjoint T F := by
    apply Finset.disjoint_left.mpr
    intro z hzT hzF
    have ht : z.1 = true := by
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hzT).1
    have hf : z.1 = false := by
      exact Finset.mem_singleton.mp (Finset.mem_product.mp hzF).1
    exact Bool.false_ne_true (hf.symm.trans ht)
  calc
    (maskCoverGraph s t mask).degree (true,(j,a)) =
        (T ∪ F).card := by
          simp only [SimpleGraph.degree,hNeighbors]
    _ = T.card + F.card :=
      Finset.card_union_of_disjoint hDisjoint
    _ = (t - 1) + t * (mask j).card := by
      simp [T,F,Finset.card_product,Nat.mul_comm]

/-- A regular all-or-nothing clique cover has equal mask size
for all outside clique indices. No transitivity on the outside
classes (or coherence of EPPA lifts) is required. -/
theorem maskCoverGraph_regular_forces_equal_mask_cards {s t d : ℕ}
    (mask : Fin s → Finset (Fin s))
    (ht : 0 < t)
    (hRegular : (maskCoverGraph s t mask).IsRegularOfDegree d)
    (i j : Fin s) :
    (mask i).card = (mask j).card := by
  let a : Fin t := ⟨0,ht⟩
  have hi := hRegular (true,(i,a))
  have hj := hRegular (true,(j,a))
  rw [maskCoverGraph_right_degree mask i a] at hi
  rw [maskCoverGraph_right_degree mask j a] at hj
  have hProduct : t * (mask i).card = t * (mask j).card := by
    omega
  exact Nat.mul_left_cancel ht hProduct

end EPPAIII.CliqueCovers
