import EPPAIII.BlockSystems.ClosedConnectedComponents
import EPPAIII.EPPA.OutsideCardinality

/-!
# Transporting a separated connected half by vertex transitivity

Suppose a finite graph H is vertex-transitive and contains an
induced preconnected graph G on exactly half of its vertices.
If no edges join the chosen copy of G to its complement,
that selected copy is one complete connected component.
An automorphism carrying one selected vertex outside sends
the entire component bijectively onto the entire outside half.

We construct the resulting *actual* equivalence between the
base vertices and outside vertices. It identifies the induced
outside graph with G, without presupposing a partition into
components or a coherent EPPA action. This statement does not
require EPPA at all; it only uses vertex transitivity.
-/

namespace EPPAIII.BlockSystems

/-- The complement of a graph automorphism is again a graph
automorphism, using the genuine irreflexive graph complement. -/
theorem graphAutomorphism_complement
    {W : Type*} (H : SimpleGraph W)
    (q : Equiv.Perm W)
    (hq : IsGraphAutomorphism H q) :
    IsGraphAutomorphism Hᶜ q := by
  intro a b
  simp only [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne,hnot⟩
    exact ⟨q.injective.ne hne,
      fun hadj => hnot ((hq a b).mpr hadj)⟩
  · rintro ⟨hne,hnot⟩
    exact ⟨fun heq => hne (congrArg q heq),
      fun hadj => hnot ((hq a b).mp hadj)⟩

/-- Vertex transitivity is preserved by graph complementation. -/
theorem transitive_complement
    {W : Type*} (H : SimpleGraph W)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H) :
    CliqueCovers.HasTransitiveGraphAutomorphisms Hᶜ := by
  intro u v
  obtain ⟨q,hq,hqu⟩ := hTrans u v
  exact ⟨q,graphAutomorphism_complement H q hq,hqu⟩

/-- An induced embedding remains induced after simultaneously
complementing the base and the host graphs. -/
theorem induced_embedding_complement
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e) :
    IsInducedGraphEmbedding Gᶜ Hᶜ e := by
  intro x y
  simp only [SimpleGraph.compl_adj]
  constructor
  · rintro ⟨hne,hnot⟩
    exact ⟨e.injective.ne hne,
      fun hadj => hnot ((he x y).mpr hadj)⟩
  · rintro ⟨hne,hnot⟩
    exact ⟨fun h => hne (congrArg e h),
      fun hadj => hnot ((he x y).mp hadj)⟩

/-- A connected induced half with no edges leaving it is
isomorphic to the entire other half under vertex transitivity.
The outside equivalence is constructed from one actual host
automorphism and fixes the original selected graph type. -/
theorem transitive_outside_equiv_of_connected_separated
    {V W : Type*} [Fintype V] [Nonempty V] [Fintype W]
    (G : SimpleGraph V)
    (hConn : G.Preconnected)
    (H : SimpleGraph W)
    (e : V ↪ W)
    (he : IsInducedGraphEmbedding G H e)
    (hDouble : Fintype.card W = 2 * Fintype.card V)
    (hTrans : CliqueCovers.HasTransitiveGraphAutomorphisms H)
    (hSeparated : ∀ u : W, u ∈ finiteOutside e →
      ∀ x : V, ¬ H.Adj u (e x)) :
    ∃ f : V ≃ {u : W // u ∈ finiteOutside e},
      H.comap (fun x => (f x).val) = G := by
  classical
  have hOutsideCard : (finiteOutside e).card = Fintype.card V := by
    rw [finiteOutside_card, hDouble]
    omega
  have hOutsidePositive : 0 < (finiteOutside e).card := by
    rw [hOutsideCard]
    exact Fintype.card_pos
  obtain ⟨w,hw⟩ := Finset.card_pos.mp hOutsidePositive
  let x0 : V := Classical.choice ‹Nonempty V›
  obtain ⟨q,hq,hqw⟩ := hTrans (e x0) w

  have hOutsideClosed :
      ∀ u ∈ (finiteOutside e : Set W), ∀ v : W,
        H.Adj u v → v ∈ (finiteOutside e : Set W) := by
    intro u hu v huv
    have hNotRange : v ∉ Set.range e := by
      intro hv
      obtain ⟨x,hx⟩ := hv
      exact (hSeparated u hu x) (by simpa [hx] using huv)
    simpa [finiteOutside] using hNotRange

  let eHom : G →g H :=
    { toFun := e
      map_rel' := by
        intro x y hxy
        exact (he x y).mp hxy }
  have hSelectedReach (x : V) : H.Reachable (e x0) (e x) :=
    (hConn x0 x).map eHom

  have hImageOutside (x : V) : q (e x) ∈ finiteOutside e := by
    have hReach : H.Reachable (q (e x0)) (q (e x)) :=
      (graphAutomorphism_reachable_iff H q hq (e x0) (e x)).mpr
        (hSelectedReach x)
    apply reachable_mem_of_adj_closed
      H (finiteOutside e : Set W) hOutsideClosed
      (q (e x0)) (q (e x))
    · simpa [hqw] using hw
    · exact hReach

  let f : V → {u : W // u ∈ finiteOutside e} :=
    fun x => ⟨q (e x), hImageOutside x⟩
  have hfInj : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply q.injective
    exact congrArg Subtype.val hxy
  have hCardEq :
      Fintype.card V =
        Fintype.card {u : W // u ∈ finiteOutside e} := by
    rw [Fintype.card_coe]
    exact hOutsideCard.symm
  let phi : V ≃ {u : W // u ∈ finiteOutside e} :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr
        ⟨hfInj,hCardEq⟩)
  refine ⟨phi,?_⟩
  apply SimpleGraph.ext
  funext x y
  apply propext
  calc
    H.Adj (phi x).val (phi y).val ↔
        H.Adj (q (e x)) (q (e y)) := Iff.rfl
    _ ↔ H.Adj (e x) (e y) := (hq (e x) (e y)).symm
    _ ↔ G.Adj x y := (he x y).symm

end EPPAIII.BlockSystems
