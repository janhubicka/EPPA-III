import EPPAIII.BlockSystems.RookThreeBase

/-!
# Concrete automorphism subgroup of the nine-vertex rook graph

Each of the six permutations of Fin 3 is explicitly represented by
an index in Fin 6: the identity, the three transpositions and the
two nontrivial cyclic rotations. A parameter in
Fin 6 × Fin 6 × Bool independently permutes rows and columns and
optionally transposes the two coordinates.

We construct actual graph automorphisms, not merely functions on
vertex subsets. Their induced subset orbits can therefore be used
with EPPA. The finite parameter space has cardinality 72.
-/

namespace EPPAIII.BlockSystems

/-- Six concrete permutations of three points. -/
def rookSmallPerm (i : Fin 6) : Equiv.Perm (Fin 3) :=
  if i = 0 then Equiv.refl _
  else if i = 1 then Equiv.swap 0 1
  else if i = 2 then Equiv.swap 0 2
  else if i = 3 then Equiv.swap 1 2
  else if i = 4 then Equiv.addRight 1
  else Equiv.addRight 2

/-- The 72 indexed row/column permutations and transpose choices. -/
abbrev rookAutParameter := Fin 6 × Fin 6 × Bool

def rookParameterizedAut (p : rookAutParameter) :
    Equiv.Perm (Fin 3 × Fin 3) :=
  let q := Equiv.prodCongr (rookSmallPerm p.1) (rookSmallPerm p.2.1)
  if p.2.2 = true then
    (Equiv.prodComm (Fin 3) (Fin 3)).trans q
  else q

/-- Independently permuting row and column coordinates preserves
the genuine adjacency relation of the rook graph. -/
theorem rook_product_perm_graph_automorphism
    (r c : Equiv.Perm (Fin 3)) :
    IsGraphAutomorphism rookThreeGraph (Equiv.prodCongr r c) := by
  let q := Equiv.prodCongr r c
  intro u v
  change (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)) ↔
    (q u ≠ q v ∧ (r u.1 = r v.1 ∨ c u.2 = c v.2))
  constructor
  · rintro ⟨hne,h⟩
    exact ⟨q.injective.ne hne,
      h.elim (fun e => Or.inl (congrArg r e))
        (fun e => Or.inr (congrArg c e))⟩
  · rintro ⟨hne,h⟩
    exact ⟨fun e => hne (congrArg q e),
      h.elim (fun e => Or.inl (r.injective e))
        (fun e => Or.inr (c.injective e))⟩

/-- Transposing rows and columns preserves adjacency. -/
theorem rook_transpose_graph_automorphism :
    IsGraphAutomorphism rookThreeGraph
      (Equiv.prodComm (Fin 3) (Fin 3)) := by
  let q := Equiv.prodComm (Fin 3) (Fin 3)
  intro u v
  change (u ≠ v ∧ (u.1 = v.1 ∨ u.2 = v.2)) ↔
    (q u ≠ q v ∧ (u.2 = v.2 ∨ u.1 = v.1))
  constructor
  · rintro ⟨hne,h⟩
    exact ⟨q.injective.ne hne,h.symm⟩
  · rintro ⟨hne,h⟩
    exact ⟨fun e => hne (congrArg q e),h.symm⟩

/-- Every indexed row/column operation is a genuine R3 automorphism. -/
theorem rookParameterizedAut_graph_automorphism
    (p : rookAutParameter) :
    IsGraphAutomorphism rookThreeGraph (rookParameterizedAut p) := by
  let q := Equiv.prodCongr (rookSmallPerm p.1) (rookSmallPerm p.2.1)
  have hq : IsGraphAutomorphism rookThreeGraph q :=
    rook_product_perm_graph_automorphism _ _
  by_cases hp : p.2.2 = true
  · have ht := rook_transpose_graph_automorphism
    have hComp : IsGraphAutomorphism rookThreeGraph
        ((Equiv.prodComm (Fin 3) (Fin 3)).trans q) := by
      intro u v
      exact (ht u v).trans
        (hq ((Equiv.prodComm (Fin 3) (Fin 3)) u)
            ((Equiv.prodComm (Fin 3) (Fin 3)) v))
    simpa [rookParameterizedAut, hp, q] using hComp
  · simpa [rookParameterizedAut, hp, q] using hq

/-- The finite subset orbit induced by the 72 genuine automorphisms. -/
def rookSubsetOrbit (S : Finset (Fin 3 × Fin 3)) :
    Finset (Finset (Fin 3 × Fin 3)) :=
  (Finset.univ : Finset rookAutParameter).image
    (fun p => S.image (rookParameterizedAut p))

/-- Every subset in such an orbit has the size of its representative. -/
theorem rookSubsetOrbit_card_preserved
    (S T : Finset (Fin 3 × Fin 3))
    (hT : T ∈ rookSubsetOrbit S) :
    T.card = S.card := by
  classical
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hT
  exact Finset.card_image_of_injective S (rookParameterizedAut p).injective

end EPPAIII.BlockSystems
