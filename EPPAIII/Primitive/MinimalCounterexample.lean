import EPPAIII.Primitive.EvenLocalRankThree
import EPPAIII.EPPA.ComplementTransport
import EPPAIII.DoubleCover.CompleteTaylor

/-!
# Minimal counterexample reduction for the primitive classification

The induction ranges over actual EPPA pairs and their selected embeddings.
The conclusion about smaller hosts therefore applies to the selected
subconstituent pair. The external rank-three catalogue is unnecessary for
this reduction.
-/

namespace EPPAIII.Primitive

open EPPAIII.BlockSystems
open EPPAIII.CliqueCovers
open EPPAIII.DoubleCover

universe u v

set_option linter.checkUnivs false in
/-- A classification predicate can mention the selected embedding. -/
abbrev PairClassification :=
  ∀ {V : Type u} {W : Type v}, SimpleGraph V → SimpleGraph W → (V ↪ W) → Prop

/-- Hypotheses on a pair for the forward direction of the classification. -/
structure SmallEPPAPair {V : Type u} {W : Type v}
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) : Prop where
  eppa : IsEPPAEmbedding G H e
  transitive : HasTransitiveGraphAutomorphisms H
  halfOrder : Nat.card W ≤ 2 * Nat.card V

/-- Minimality over all smaller transitive hosts, including imprimitive ones. -/
structure MinimalCounterexample (classified : PairClassification.{u, v})
    {V : Type u} {W : Type v} (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W) :
    Prop where
  pair : SmallEPPAPair G H e
  unclassified : ¬ classified G H e
  smaller : ∀ {X : Type u} {Y : Type v} [Finite X] [Finite Y]
    (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
    Nat.card Y < Nat.card W → SmallEPPAPair A B f → classified A B f

private def hasCounterexampleAtOrder (classified : PairClassification.{u, v})
    (n : ℕ) : Prop :=
  ∃ (V : Type u) (W : Type v) (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W),
    Finite V ∧ Finite W ∧ Nat.card W = n ∧ SmallEPPAPair G H e ∧ ¬ classified G H e

/-- If the forward classification fails at an actual finite pair, it fails
at such a pair of minimal host order. -/
theorem exists_minimalCounterexample (classified : PairClassification.{u, v})
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hPair : SmallEPPAPair G H e) (hBad : ¬ classified G H e) :
    ∃ (X : Type u) (Y : Type v) (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      Finite X ∧ Finite Y ∧ Nat.card Y ≤ Nat.card W ∧ MinimalCounterexample classified A B f := by
  classical
  have hEx : ∃ n, hasCounterexampleAtOrder classified n :=
    ⟨Nat.card W, V, W, G, H, e, ‹Finite V›, ‹Finite W›, rfl, hPair, hBad⟩
  obtain ⟨X, Y, A, B, f, hFinX, hFinY, hCard, hNewPair, hNewBad⟩ := Nat.find_spec hEx
  refine ⟨X, Y, A, B, f, hFinX, hFinY, ?_, ⟨hNewPair, hNewBad, ?_⟩⟩
  · rw [hCard]
    exact Nat.find_min' hEx
      ⟨V, W, G, H, e, ‹Finite V›, ‹Finite W›, rfl, hPair, hBad⟩
  · intro X' Y' hFinX' hFinY' A' B' f' hLt hPair'
    by_contra hBad'
    apply Nat.find_min hEx (by simpa only [← hCard] using hLt)
    exact ⟨X', Y', A', B', f', hFinX', hFinY', rfl, hPair', hBad'⟩

/-- Both graphs are complemented and the actual embedding is retained. -/
theorem MinimalCounterexample.compl {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : MinimalCounterexample classified G H e)
    (hCompl : ∀ {X : Type u} {Y : Type v} (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      classified A B f ↔ classified Aᶜ Bᶜ f) :
    MinimalCounterexample classified Gᶜ Hᶜ e :=
  ⟨⟨eppa_embedding_complement G H e h.pair.eppa,
    transitive_complement H h.pair.transitive, h.pair.halfOrder⟩,
    fun hc => h.unclassified ((hCompl G H e).mpr hc), h.smaller⟩

/-- Orient a counterexample so the chosen root has at most as many
neighbors as distinct nonneighbors. In a transitive graph this is the
usual bound on the valency. -/
theorem MinimalCounterexample.orient {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : MinimalCounterexample classified G H e) (root : V)
    (hCompl : ∀ {X : Type u} {Y : Type v} (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      classified A B f ↔ classified Aᶜ Bᶜ f) :
    (2 * Nat.card (H.neighborSet (e root)) + 1 ≤ Nat.card W) ∨
      (MinimalCounterexample classified Gᶜ Hᶜ e ∧
        2 * Nat.card (Hᶜ.neighborSet (e root)) + 1 ≤ Nat.card W) := by
  have hOrder := order_eq_one_add_subconstituent_orders H (e root)
  change Nat.card W = 1 + Nat.card (H.neighborSet (e root)) +
    Nat.card (Hᶜ.neighborSet (e root)) at hOrder
  by_cases hLe : 2 * Nat.card (H.neighborSet (e root)) + 1 ≤ Nat.card W
  · exact Or.inl hLe
  · exact Or.inr ⟨h.compl hCompl, by omega⟩

/-- A minimal counterexample falls into the primitive rank-three branch
when the homogeneous and imprimitive parts of the classification are known. -/
theorem MinimalCounterexample.primitive_rankThree {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : MinimalCounterexample classified G H e)
    (hHomogeneous : IsHomogeneousGraph H → classified G H e)
    (hImprimitive : ¬ IsPrimitiveAutAction H → SmallEPPAPair G H e → classified G H e) :
    IsPrimitiveAutAction H ∧ HasRankThreeAutAction H := by
  classical
  have hPrimitive : IsPrimitiveAutAction H :=
    by_contradiction fun hn => h.unclassified (hImprimitive hn h.pair)
  let := Fintype.ofFinite V
  let := Fintype.ofFinite W
  have hBound : Fintype.card W ≤ 2 * Fintype.card V := by
    simpa only [← Nat.card_eq_fintype_card] using h.pair.halfOrder
  obtain hTop | hBot | hRank := transitive_eppa_at_most_double_clique_empty_or_rank_three
    G H e h.pair.eppa h.pair.transitive hBound (fun _ => hPrimitive)
  · exact False.elim (h.unclassified (hHomogeneous (homogeneous_of_complete H
      (by rw [hTop]; exact fun _ _ hne => hne))))
  · exact False.elim (h.unclassified (hHomogeneous (homogeneous_of_edgeless H
      (by rw [hBot]; exact fun _ _ hAdj => hAdj))))
  · exact ⟨hPrimitive, hRank⟩

/-- Failure of the forward classification yields an oriented minimal
primitive rank-three counterexample, with a selected root. The only case
inputs are the already separated homogeneous and imprimitive results
and complement closure of the proposed classification. -/
theorem exists_oriented_primitive_rankThree_minimalCounterexample
    (classified : PairClassification.{u, v})
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : V ↪ W)
    (hPair : SmallEPPAPair G H e) (hBad : ¬ classified G H e)
    (hHomogeneous : ∀ {X : Type u} {Y : Type v} [Finite X] [Finite Y]
      (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      IsHomogeneousGraph B → SmallEPPAPair A B f → classified A B f)
    (hImprimitive : ∀ {X : Type u} {Y : Type v} [Finite X] [Finite Y]
      (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      ¬ IsPrimitiveAutAction B → SmallEPPAPair A B f → classified A B f)
    (hCompl : ∀ {X : Type u} {Y : Type v} (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y),
      classified A B f ↔ classified Aᶜ Bᶜ f) :
    ∃ (X : Type u) (Y : Type v) (A : SimpleGraph X) (B : SimpleGraph Y) (f : X ↪ Y) (root : X),
      Finite X ∧ Finite Y ∧ Nat.card Y ≤ Nat.card W ∧ MinimalCounterexample classified A B f ∧
      IsPrimitiveAutAction B ∧ HasRankThreeAutAction B ∧
      2 * Nat.card (B.neighborSet (f root)) + 1 ≤ Nat.card Y := by
  obtain ⟨X, Y, A, B, f, hFinX, hFinY, hSize, hMin⟩ :=
    exists_minimalCounterexample classified G H e hPair hBad
  let := hFinX
  let := hFinY
  obtain ⟨hPrimitive, hRank⟩ := hMin.primitive_rankThree
    (fun h => hHomogeneous A B f h hMin.pair) (hImprimitive A B f)
  obtain ⟨b, _, _⟩ := hRank.1
  have hPosY : 0 < Nat.card Y := Nat.card_pos_iff.mpr ⟨⟨b⟩, hFinY⟩
  have hBound := hMin.pair.halfOrder
  obtain ⟨root⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card X by omega)).1
  obtain hOrientation | ⟨hMin', hOrientation⟩ := hMin.orient root hCompl
  · exact ⟨X, Y, A, B, f, root, hFinX, hFinY, hSize, hMin, hPrimitive, hRank, hOrientation⟩
  · obtain ⟨hPrimitive', hRank'⟩ := hMin'.primitive_rankThree
      (fun h => hHomogeneous Aᶜ Bᶜ f h hMin'.pair) (hImprimitive Aᶜ Bᶜ f)
    exact ⟨X, Y, Aᶜ, Bᶜ, f, root, hFinX, hFinY, hSize, hMin',
      hPrimitive', hRank', hOrientation⟩

/-- At every selected root of a minimal rank-three counterexample,
each half-order subconstituent is already classified for its actual
selected embedding. -/
theorem MinimalCounterexample.classified_subconstituents
    {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : MinimalCounterexample classified G H e) (hRank : HasRankThreeAutAction H)
    (root : V) :
    (Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) →
      classified (localGraph G root) (localGraph H (e root))
        (restrictEmbedding e (fun x hx => (h.pair.eppa.1 root x).mp hx))) ∧
    (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} →
      classified (nonlocalGraph G root) (nonlocalGraph H (e root))
        (restrictEmbedding e (fun x hx =>
          ⟨e.injective.ne hx.1, (h.pair.eppa.1 root x).not.mp hx.2⟩))) := by
  have hOrder := order_eq_one_add_subconstituent_orders H (e root)
  have hLocal := localGraph_transitive H hRank (e root)
  have hNonlocal := nonlocalGraph_transitive H hRank (e root)
  constructor
  · intro hHalf
    exact h.smaller _ _ _ (by omega) ⟨local_eppa G H e h.pair.eppa root, hLocal, hHalf⟩
  · intro hHalf
    have hSmaller : Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} < Nat.card W := by
      omega
    exact h.smaller _ _ _ hSmaller ⟨nonlocal_eppa G H e h.pair.eppa root, hNonlocal, hHalf⟩

/-- At least one of the actual selected subconstituents meets the
half-order bound and is classified by minimality. -/
theorem MinimalCounterexample.classified_half_subconstituent
    {classified : PairClassification.{u, v}}
    {V : Type u} {W : Type v} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} {e : V ↪ W}
    (h : MinimalCounterexample classified G H e) (hRank : HasRankThreeAutAction H)
    (root : V) :
    (Nat.card (H.neighborSet (e root)) ≤ 2 * Nat.card (G.neighborSet root) ∧
      classified (localGraph G root) (localGraph H (e root))
        (restrictEmbedding e (fun x hx => (h.pair.eppa.1 root x).mp hx))) ∨
    (Nat.card {x : W // e root ≠ x ∧ ¬ H.Adj (e root) x} ≤
        2 * Nat.card {x : V // root ≠ x ∧ ¬ G.Adj root x} ∧
      classified (nonlocalGraph G root) (nonlocalGraph H (e root))
        (restrictEmbedding e (fun x hx =>
          ⟨e.injective.ne hx.1, (h.pair.eppa.1 root x).not.mp hx.2⟩))) := by
  obtain ⟨hLocal, hOther⟩ := h.classified_subconstituents hRank root
  obtain hHalf | hHalf := selected_subconstituent_at_least_half G H e root
    h.pair.transitive h.pair.halfOrder
  · exact Or.inl ⟨hHalf, hLocal hHalf⟩
  · exact Or.inr ⟨hHalf, hOther hHalf⟩

/-- The two alternatives for nonhomogeneous subconstituents in the
minimal-counterexample reduction. The exact-half hypotheses need only
be applied when the corresponding selected copy meets the half-order
bound. They are supplied by the host classification and cover bounds. -/
theorem subconstituent_exactHalves_or_mixedParity
    {hostLocal hostOther selectedLocal selectedOther : ℕ}
    (hTotal : 1 + hostLocal + hostOther ≤ 2 * (1 + selectedLocal + selectedOther))
    (hHalf : hostLocal ≤ 2 * selectedLocal ∨ hostOther ≤ 2 * selectedOther)
    (hLocal : hostLocal ≤ 2 * selectedLocal → 2 * selectedLocal = hostLocal)
    (hOther : hostOther ≤ 2 * selectedOther → 2 * selectedOther = hostOther) :
    (2 * selectedLocal = hostLocal ∧ 2 * selectedOther = hostOther) ∨
      (2 * selectedLocal = hostLocal ∧ hostOther % 2 = 1) ∨
      (hostLocal % 2 = 1 ∧ 2 * selectedOther = hostOther) := by
  rcases hHalf with hHalf | hHalf
  · have hEq := hLocal hHalf
    by_cases hHalf' : hostOther ≤ 2 * selectedOther
    · exact Or.inl ⟨hEq, hOther hHalf'⟩
    · exact Or.inr (Or.inl ⟨hEq, by omega⟩)
  · have hEq := hOther hHalf
    by_cases hHalf' : hostLocal ≤ 2 * selectedLocal
    · exact Or.inl ⟨hLocal hHalf', hEq⟩
    · exact Or.inr (Or.inr ⟨by omega, hEq⟩)

end EPPAIII.Primitive
