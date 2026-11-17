import EPPAIII.CliqueCovers.Basic
import EPPAIII.Primitive.RookModel
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Pi

/-! # The nine-vertex rook obstruction for Grassmann constituents -/

namespace EPPAIII.Primitive

open SimpleGraph

private def MonochromaticPath {V : Type*} (G : SimpleGraph V) (side : V → Bool) : Prop :=
  ∃ a b c, a ≠ c ∧ side a = side b ∧ side b = side c ∧
    G.Adj a b ∧ G.Adj b c ∧ ¬ G.Adj a c

private instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (side : V → Bool) : Decidable (MonochromaticPath G side) := by
  unfold MonochromaticPath
  infer_instance

private instance (n : ℕ) : DecidableRel (rookGraph n).Adj :=
  fun x y => inferInstanceAs (Decidable (x ≠ y ∧ (x.1 = y.1 ∨ x.2 = y.2)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rookThree_monochromatic_path :
    ∀ (side : Fin 3 × Fin 3 → Bool), MonochromaticPath (rookGraph 3) side := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem rookThree_compl_monochromatic_path :
    ∀ (side : Fin 3 × Fin 3 → Bool), MonochromaticPath (rookGraph 3)ᶜ side := by
  decide

private theorem no_embedding_of_monochromatic_path {U V : Type*}
    {G : SimpleGraph U} {H : SimpleGraph V}
    (hPath : ∀ side : U → Bool, MonochromaticPath G side)
    (side : V → Bool)
    (hCluster : ∀ {a b c : V}, a ≠ c → side a = side b → side b = side c →
      H.Adj a b → H.Adj b c → H.Adj a c) :
    IsEmpty (G ↪g H) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨a, b, c, hac, habSide, hbcSide, hab, hbc, hnac⟩ := hPath (fun x => side (f x))
  exact hnac (f.map_adj_iff.mp (hCluster (f.injective.ne hac) habSide hbcSide
    (f.map_adj_iff.mpr hab) (f.map_adj_iff.mpr hbc)))

private theorem no_embedding_in_clique_union {U : Type*} {G : SimpleGraph U}
    (hPath : ∀ side : U → Bool, MonochromaticPath G side) (s t : ℕ) :
    IsEmpty (G ↪g cliqueUnion s t) := by
  apply no_embedding_of_monochromatic_path hPath (fun _ => false)
  intro a b c hac _ _ hab hbc
  have hIndex : a.1 = c.1 := hab.1.trans hbc.1
  exact ⟨hIndex, fun hCoordinate => hac (Prod.ext hIndex hCoordinate)⟩

private theorem no_embedding_in_cover {U : Type*} {G : SimpleGraph U}
    (hPath : ∀ side : U → Bool, MonochromaticPath G side) (s t : ℕ)
    (X : CrossType) (Y : Bool) :
    IsEmpty (G ↪g coverGraph s t X Y) := by
  apply no_embedding_of_monochromatic_path hPath Prod.fst
  intro a b c hac habSide hbcSide hab hbc
  have hAB := hab.resolve_right (fun h => h.1 habSide)
  have hBC := hbc.resolve_right (fun h => h.1 hbcSide)
  have hSide : a.1 = c.1 := habSide.trans hbcSide
  have hIndex : a.2.1 = c.2.1 := hAB.2.1.trans hBC.2.1
  exact Or.inl ⟨hSide, hIndex, fun hCoordinate =>
    hac (Prod.ext hSide (Prod.ext hIndex hCoordinate))⟩

/-- An induced copy of the nine-vertex rook graph excludes clique unions and
their complements. Each colouring of the rook graph or its complement
contains a monochromatic induced three-vertex path. -/
theorem no_clique_union_or_compl_of_induced_rookThree {V : Type*} {G : SimpleGraph V}
    (f : rookGraph 3 ↪g G) (s t : ℕ) :
    IsEmpty (G ≃g cliqueUnion s t) ∧ IsEmpty (G ≃g (cliqueUnion s t)ᶜ) := by
  refine ⟨⟨fun φ => (no_embedding_in_clique_union rookThree_monochromatic_path s t).false
    (φ.toEmbedding.comp f)⟩, ⟨fun φ => ?_⟩⟩
  have f' : (rookGraph 3)ᶜ ↪g cliqueUnion s t := by
    simpa only [compl_compl] using Embedding.complEquiv (φ.toEmbedding.comp f)
  exact (no_embedding_in_clique_union rookThree_compl_monochromatic_path s t).false f'

/-- An induced copy of the nine-vertex rook graph excludes generalized
clique covers in both orientations. -/
theorem no_cover_or_compl_of_induced_rookThree {V : Type*} {G : SimpleGraph V}
    (f : rookGraph 3 ↪g G) (s t : ℕ) (X : CrossType) (Y : Bool) :
    IsEmpty (G ≃g coverGraph s t X Y) ∧ IsEmpty (G ≃g (coverGraph s t X Y)ᶜ) := by
  refine ⟨⟨fun φ => (no_embedding_in_cover rookThree_monochromatic_path s t X Y).false
    (φ.toEmbedding.comp f)⟩, ⟨fun φ => ?_⟩⟩
  have f' : (rookGraph 3)ᶜ ↪g coverGraph s t X Y := by
    simpa only [compl_compl] using Embedding.complEquiv (φ.toEmbedding.comp f)
  exact (no_embedding_in_cover rookThree_compl_monochromatic_path s t X Y).false f'

end EPPAIII.Primitive
