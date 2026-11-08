import EPPAIII.EPPA.Hereditary

/-!
# Recovering line-graph incidence stars from focused triples

A selected edge is represented by a two-element finset of ground points.
Two distinct such edges share at most one endpoint. When they share an
endpoint v, the focused-triple predicate with a third selected edge
recovers exactly the set of all selected edges containing v.

The final theorem transports this incidence signature between two
indexed selected-edge families from pair-intersection and triple-focus
data. This is the first structural step of the triangular-graph
reconstruction proof; it does not yet construct the full ground-point
permutation.
-/

namespace EPPAIII.LineGraph

/-- Three selected edges focus at one common ground point. -/
def FocusedAt {I V : Type*} (E : I → Finset V)
    (i j k : I) : Prop :=
  ∃ v : V, v ∈ E i ∧ v ∈ E j ∧ v ∈ E k

/-- Distinct two-point edge sets have at most one common endpoint. -/
theorem distinct_two_edges_unique_shared_point
    {V : Type*} [DecidableEq V]
    (a b : Finset V)
    (ha : a.card = 2) (hb : b.card = 2) (hab : a ≠ b)
    (x y : V)
    (hxa : x ∈ a) (hxb : x ∈ b)
    (hya : y ∈ a) (hyb : y ∈ b) :
    x = y := by
  by_contra hxy
  have hpair : ({x,y} : Finset V).card = 2 :=
    Finset.card_pair hxy
  have hsuba : ({x,y} : Finset V) ⊆ a := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxa
    · exact hya
  have hsubb : ({x,y} : Finset V) ⊆ b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxb
    · exact hyb
  have heqa : ({x,y} : Finset V) = a :=
    Finset.eq_of_subset_of_card_le hsuba (by simp [ha, hpair])
  have heqb : ({x,y} : Finset V) = b :=
    Finset.eq_of_subset_of_card_le hsubb (by simp [hb, hpair])
  exact hab (heqa.symm.trans heqb)

/-- Every selected edge containing the unique common point of two
distinct edges is detected by a focused triple, and conversely. -/
theorem focused_iff_contains_common_point
    {I V : Type*}
    (E : I → Finset V)
    (i j k : I) (v : V)
    (hvi : v ∈ E i) (hvj : v ∈ E j)
    (hUnique : ∀ w : V, w ∈ E i → w ∈ E j → w = v) :
    FocusedAt E i j k ↔ v ∈ E k := by
  constructor
  · rintro ⟨w,hwi,hwj,hwk⟩
    rw [hUnique w hwi hwj] at hwk
    exact hwk
  · intro hvk
    exact ⟨v,hvi,hvj,hvk⟩

/-- Incidence with a shared endpoint is preserved under matching
pair-intersection and focused-triple information. Neither a
permutation of points nor a selected-star labelling is assumed. -/
theorem shared_endpoint_signature_preserved
    {I V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (E : I → Finset V) (F : I → Finset W)
    (hEcard : ∀ i, (E i).card = 2)
    (hFcard : ∀ i, (F i).card = 2)
    (hEinj : Function.Injective E)
    (hFinj : Function.Injective F)
    (i j : I) (hij : i ≠ j)
    (v : V) (w : W)
    (hvi : v ∈ E i) (hvj : v ∈ E j)
    (hwi : w ∈ F i) (hwj : w ∈ F j)
    (hFocus : ∀ k, FocusedAt E i j k ↔ FocusedAt F i j k)
    (k : I) :
    v ∈ E k ↔ w ∈ F k := by
  have hEne : E i ≠ E j := fun h => hij (hEinj h)
  have hFne : F i ≠ F j := fun h => hij (hFinj h)
  have hEunique : ∀ u : V, u ∈ E i → u ∈ E j → u = v := by
    intro u hui huj
    exact distinct_two_edges_unique_shared_point
      (E i) (E j) (hEcard i) (hEcard j) hEne
      u v hui huj hvi hvj
  have hFunique : ∀ u : W, u ∈ F i → u ∈ F j → u = w := by
    intro u hui huj
    exact distinct_two_edges_unique_shared_point
      (F i) (F j) (hFcard i) (hFcard j) hFne
      u w hui huj hwi hwj
  calc
    v ∈ E k ↔ FocusedAt E i j k :=
      (focused_iff_contains_common_point E i j k v
        hvi hvj hEunique).symm
    _ ↔ FocusedAt F i j k := hFocus k
    _ ↔ w ∈ F k :=
      focused_iff_contains_common_point F i j k w
        hwi hwj hFunique

/-- A shared point in the source family gives a shared point in the
target family with exactly the same indexed incidence signature.
This is the usable reconstruction interface for the next step. -/
theorem shared_point_has_matching_signature
    {I V W : Type*}
    [DecidableEq V] [DecidableEq W]
    (E : I → Finset V) (F : I → Finset W)
    (hEcard : ∀ i, (E i).card = 2)
    (hFcard : ∀ i, (F i).card = 2)
    (hEinj : Function.Injective E)
    (hFinj : Function.Injective F)
    (hPair : ∀ i j, (∃ v, v ∈ E i ∧ v ∈ E j) ↔
                         (∃ w, w ∈ F i ∧ w ∈ F j))
    (hFocus : ∀ i j k,
       FocusedAt E i j k ↔ FocusedAt F i j k)
    (i j : I) (hij : i ≠ j) (v : V)
    (hvi : v ∈ E i) (hvj : v ∈ E j) :
    ∃ w : W, w ∈ F i ∧ w ∈ F j ∧
      (∀ k, v ∈ E k ↔ w ∈ F k) := by
  obtain ⟨w,hwi,hwj⟩ := (hPair i j).mp ⟨v,hvi,hvj⟩
  refine ⟨w,hwi,hwj,?_⟩
  intro k
  exact shared_endpoint_signature_preserved
    E F hEcard hFcard hEinj hFinj
    i j hij v w hvi hvj hwi hwj (hFocus i j) k

end EPPAIII.LineGraph
