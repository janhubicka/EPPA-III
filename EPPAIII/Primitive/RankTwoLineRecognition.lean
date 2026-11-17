import EPPAIII.BlockSystems.ClusterObstructions
import EPPAIII.BlockSystems.SmallHostRankThreeStatement
import EPPAIII.CliqueCovers.Basic
import EPPAIII.Primitive.SmallConstituentGraphScreen
import EPPAIII.Primitive.Subconstituents
import Mathlib.Combinatorics.SimpleGraph.Clique

/-! # Recovering the rank-two local chart from a line -/

namespace EPPAIII.Primitive

open SimpleGraph EPPAIII.BlockSystems
attribute [local instance] Classical.propDecidable

private theorem regularCluster_iso_cliqueUnion {V : Type*} [Fintype V]
    (J : SimpleGraph V) {s q : ℕ} (hq : 0 < q) (hSize : Fintype.card V = s * q)
    (hDegree : J.IsRegularOfDegree (q - 1)) (hCluster : IsClusterGraph J) :
    Nonempty (J ≃g cliqueUnion s q) := by
  classical
  let relation : Setoid V :=
    ⟨fun x y => x = y ∨ J.Adj x y,
     ⟨fun x => Or.inl rfl, (by
       intro x y h
       exact h.imp Eq.symm J.adj_symm), (by
       intro x y z hxy hyz
       rcases hxy with rfl | hxy
       · exact hyz
       rcases hyz with rfl | hyz
       · exact Or.inr hxy
       by_cases hxz : x = z
       · exact Or.inl hxz
       · exact Or.inr (hCluster x y z hxy hyz hxz))⟩⟩
  let Q := Quotient relation
  let : Fintype Q := Fintype.ofFinite Q
  let f : V → Q := Quotient.mk relation
  have hSame (x y : V) : f x = f y ↔ x = y ∨ J.Adj x y :=
    Quotient.eq_iff_equiv
  have hFibres (b : Q) : Fintype.card {x // f x = b} = q := by
    refine Quotient.inductionOn b ?_
    intro x
    change Fintype.card {y // f y = f x} = q
    let T := insert x (J.neighborFinset x)
    have hMem (y : V) : f y = f x ↔ y ∈ T := by
      change f y = f x ↔ y ∈ insert x (J.neighborFinset x)
      rw [hSame, Finset.mem_insert, mem_neighborFinset]
      exact or_congr Iff.rfl (J.adj_comm y x)
    have hCard := Fintype.card_congr ((Equiv.refl V).subtypeEquiv hMem)
    rw [Fintype.card_coe, Finset.card_insert_of_notMem, card_neighborFinset_eq_degree,
      hDegree] at hCard
    · omega
    · simpa only [mem_neighborFinset] using J.loopless.irrefl x
  let fibreCoordinates : V ≃ Q × Fin q :=
    (Equiv.sigmaFiberEquiv f).symm.trans
      (Equiv.sigmaEquivProdOfEquiv fun b => Fintype.equivFinOfCardEq (hFibres b))
  have hProduct : Fintype.card Q * q = s * q := by
    simpa [hSize] using (Fintype.card_congr fibreCoordinates).symm
  have hQ := Nat.eq_of_mul_eq_mul_right hq hProduct
  let coordinates := fibreCoordinates.trans
    ((Fintype.equivFinOfCardEq hQ).prodCongr (Equiv.refl (Fin q)))
  refine ⟨⟨coordinates, ?_⟩⟩
  intro x y
  have hFirst : (coordinates x).1 = (coordinates y).1 ↔ f x = f y :=
    (Fintype.equivFinOfCardEq hQ).injective.eq_iff
  change ((coordinates x).1 = (coordinates y).1 ∧ (coordinates x).2 ≠ (coordinates y).2) ↔ J.Adj x y
  constructor
  · rintro ⟨h₁, h₂⟩
    rcases (hSame x y).mp (hFirst.mp h₁) with rfl | hAdj
    · exact (h₂ rfl).elim
    · exact hAdj
  · intro hAdj
    have h₁ := hFirst.mpr ((hSame x y).mpr (Or.inr hAdj))
    exact ⟨h₁, fun h₂ => hAdj.ne (coordinates.injective (Prod.ext h₁ h₂))⟩

private theorem regular_iso_cliqueUnion_of_cliques {V : Type*} [Fintype V]
    (J : SimpleGraph V) {s q : ℕ} (hq : 0 < q) (hSize : Fintype.card V = s * q)
    (hDegree : J.IsRegularOfDegree (q - 1))
    (hCliques : ∀ x : V, ∃ S : Finset V, S.card = q ∧ x ∈ S ∧ J.IsClique ↑S) :
    Nonempty (J ≃g cliqueUnion s q) := by
  classical
  apply regularCluster_iso_cliqueUnion J hq hSize hDegree
  intro a b c hab hbc hac
  obtain ⟨S, hS, hb, hClique⟩ := hCliques b
  have hNeighbours : S.erase b = J.neighborFinset b := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
      exact (J.mem_neighborFinset b y).mpr (hClique hb hy hne.symm)
    · rw [Finset.card_erase_of_mem hb, hS, card_neighborFinset_eq_degree, hDegree b]
  have hMem (x : V) (h : J.Adj b x) : x ∈ S := by
    apply Finset.mem_of_mem_erase (a := b)
    rw [hNeighbours]
    exact (J.mem_neighborFinset b x).mpr h
  exact hClique (hMem a hab.symm) (hMem c hbc) hac

/-- In a rank-three SRG, one clique of order `q + 1` determines every local
clique chart when the local degree is `q - 1`. -/
theorem localCharts_of_rankThree_line {V : Type*} [Fintype V] {n s q μ : ℕ}
    (H : SimpleGraph V) (hq : 0 < q)
    (hRank : HasRankThreeAutAction H)
    (hSRG : H.IsSRGWith n (s * q) (q - 1) μ)
    (line : Finset V) (hLineCard : line.card = q + 1) (hLine : H.IsClique ↑line) :
    ∀ r, Nonempty (localGraph H r ≃g cliqueUnion s q) := by
  classical
  intro r
  have hp := constituentGraph_profile H ⟨_, _, _, _⟩ hSRG r false
  have hCard : Fintype.card (H.neighborSet r) = s * q :=
    Nat.card_eq_fintype_card.symm.trans hp.1
  have hDegree : (localGraph H r).IsRegularOfDegree (q - 1) := by
    intro x
    rw [← (localGraph H r).card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.2 x
  apply regular_iso_cliqueUnion_of_cliques (localGraph H r) hq hCard hDegree
  intro x
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < line.card)
  obtain ⟨π, hπ, hπa, hπb⟩ := hRank.2.2.2 a b r x hab x.property.ne
    (iff_of_true (hLine ha hb hab) x.property)
  let φ : {y // y ∈ line.erase a} ↪ H.neighborSet r :=
    ⟨fun y => ⟨π y.val, by
      rw [← hπa]
      obtain ⟨hne, hy⟩ := Finset.mem_erase.mp y.property
      exact (hπ _ _).mp (hLine ha hy hne.symm)⟩,
     fun y z h => Subtype.ext (π.injective (congrArg Subtype.val h))⟩
  refine ⟨(line.erase a).attach.map φ, ?_, ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_attach, Finset.card_erase_of_mem ha, hLineCard]
    omega
  · exact Finset.mem_map.mpr ⟨⟨b, Finset.mem_erase.mpr ⟨hab.symm, hb⟩⟩,
      Finset.mem_attach _ _, Subtype.ext hπb⟩
  · intro y hy z hz hne
    obtain ⟨y', _, rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨z', _, rfl⟩ := Finset.mem_map.mp hz
    change H.Adj (π y'.val) (π z'.val)
    apply (hπ _ _).mp
    exact hLine (Finset.mem_of_mem_erase y'.property) (Finset.mem_of_mem_erase z'.property)
      (fun h => hne (congrArg φ (Subtype.ext h)))

/-- If adjacent pairs have just one common neighbour, each local graph is
a matching. The number of edges is determined by the host degree. -/
theorem localCharts_of_srg_lambda_one {V : Type*} [Fintype V] {n s μ : ℕ}
    (H : SimpleGraph V) (hSRG : H.IsSRGWith n (s * 2) 1 μ) :
    ∀ r, Nonempty (localGraph H r ≃g cliqueUnion s 2) := by
  classical
  intro r
  let J := localGraph H r
  have hp := constituentGraph_profile H ⟨n, s * 2, 1, μ⟩ hSRG r false
  have hCard : Fintype.card (H.neighborSet r) = s * 2 :=
    Nat.card_eq_fintype_card.symm.trans hp.1
  have hDegree : J.IsRegularOfDegree 1 := by
    intro x
    rw [← J.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card]
    exact hp.2 x
  apply regular_iso_cliqueUnion_of_cliques J (q := 2) (by decide) hCard hDegree
  intro x
  have hPositive : 0 < (J.neighborFinset x).card := by
    rw [J.card_neighborFinset_eq_degree, hDegree]
    decide
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hPositive
  have hxy : J.Adj x y := (J.mem_neighborFinset x y).mp hy
  refine ⟨{x, y}, by simp [hxy.ne], by simp, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact hxy
  · exact hxy.symm
  · exact (hab rfl).elim

end EPPAIII.Primitive
