import EPPAIII.BlockSystems.ExceptionalNamedModels

/-!
# The mate-free R3 blow-up is not the Taylor double

The manuscript's R3 alternatives include the Taylor double and
the complement of the two-clique extension. Since the R3 graph
is self-complementary, the latter is represented by the
mate-free rook blow-up.

Both graph models have degree eight on eighteen vertices, so
degree comparison alone cannot separate them. A more useful
intrinsic invariant is the existence of nonadjacent false twins:
the blow-up has nine canonical twin pairs, while the Taylor
double has none. These two elementary finite certificates prove
that the omitted named alternative cannot be subsumed by the
Taylor double through an unmentioned relabelling.
-/

namespace EPPAIII.BlockSystems

set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Two distinct nonadjacent vertices with identical open
neighbourhoods form a false-twin pair. -/
def HasFalseTwins {V : Type*} (J : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧
    (∀ w : V, J.Adj u w ↔ J.Adj v w)

/-- The mate-free rook blow-up contains false twins:
the two vertices over each original rook vertex. -/
theorem rook_matefree_has_false_twins :
    HasFalseTwins (rookDoubleGraph false false) := by
  refine ⟨(false,((0 : Fin 3),(0 : Fin 3))),
    (true,((0 : Fin 3),(0 : Fin 3))), by decide,
    by decide, ?_⟩
  intro w
  fin_cases w.1
  · rcases w.2 with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide
  · rcases w.2 with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> decide

/-- The canonical Taylor double of R3 has no false-twin
pair at all. This is a finite certificate on 18 vertices,
not a graph-isomorphism enumeration. -/
theorem rook_taylor_has_no_false_twins :
    ¬ HasFalseTwins (rookDoubleGraph false true) := by
  unfold HasFalseTwins
  decide

/-- False-twin existence is preserved by any graph isomorphism.
This elementary argument avoids enumerating all 18! relabellings. -/
theorem false_twins_transport_iso
    {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G ≃g H)
    (hTwins : HasFalseTwins G) :
    HasFalseTwins H := by
  obtain ⟨u,v,huv,hnuv,hTypes⟩ := hTwins
  refine ⟨f u,f v,f.injective.ne huv,?_,?_⟩
  · intro huv'
    exact hnuv ((f.map_adj_iff).mp huv')
  · intro w
    have h1 : H.Adj (f u) w ↔ G.Adj u (f.symm w) := by
      simpa using (f.map_adj_iff (v := u) (w := f.symm w))
    have h2 : H.Adj (f v) w ↔ G.Adj v (f.symm w) := by
      simpa using (f.map_adj_iff (v := v) (w := f.symm w))
    exact h1.trans ((hTypes (f.symm w)).trans h2.symm)

/-- The two 8-regular named R3 models are not isomorphic.
In particular, the mate-free complementary 2-clique-extension
alternative must not be omitted as if it were Taylor. -/
theorem rook_matefree_not_isomorphic_to_taylor :
    ¬ Nonempty
      ((rookDoubleGraph false false) ≃g
        (rookDoubleGraph false true)) := by
  rintro ⟨f⟩
  exact rook_taylor_has_no_false_twins
    (false_twins_transport_iso
      (rookDoubleGraph false false)
      (rookDoubleGraph false true) f
      rook_matefree_has_false_twins)

end EPPAIII.BlockSystems
