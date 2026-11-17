import EPPAIII.EPPA.Definitions

namespace EPPAIII

/-- The transposition a<->b preserves the induced graph on
R union {a} if a,b are outside R and have equal types into R. -/
theorem equal_types_partial_swap
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (R : Finset V) (a b : V)
    (ha : a ∉ R) (hb : b ∉ R)
    (hEqual : ∀ r ∈ R, G.Adj a r ↔ G.Adj b r) :
    EPPAIII.IsPartialGraphAutomorphism G (insert a R)
      (Equiv.swap a b) := by
  classical
  have hFix (r : V) (hr : r ∈ R) :
      (Equiv.swap a b) r = r := by
    have hra : r ≠ a := by
      intro h; exact ha (h ▸ hr)
    have hrb : r ≠ b := by
      intro h; exact hb (h ▸ hr)
    exact Equiv.swap_apply_of_ne_of_ne hra hrb
  intro u v hu hv
  simp only [Finset.mem_insert] at hu hv
  rcases hu with huEq | hu
  · subst u
    rcases hv with hvEq | hv
    · subst v
      simp
    · simpa [hFix v hv] using hEqual v hv
  · rcases hv with hvEq | hv
    · subst v
      have hh : G.Adj u a ↔ G.Adj u b :=
        (G.adj_comm u a).trans
          ((hEqual u hu).trans (G.adj_comm b u))
      simpa [hFix u hu] using hh
    · simp [hFix u hu, hFix v hv]

end EPPAIII
