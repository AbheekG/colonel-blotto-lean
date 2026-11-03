import Blotto.GeneralPaperRaySparseEvaluation

/-! The executed minimum returns a tight positive-derivative blocker and
the exact maximal forward feasible time for its finite row family. This
includes a zero endpoint and requires no strictly feasible starting point.
-/
namespace Blotto.GeneralPaperRayMinimumSound
open GeneralPaperRayAffine GeneralPaperRayMinimum
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem selected {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i) (c : Choice i)
    (hc : (scan evaluate rows).choice=some c) :
    c.blocker∈rows ∧ c.time=(evaluate c.blocker).1.crossing ∧ 0<(evaluate c.blocker).1.slope ∧
      ∀ j∈rows,0<(evaluate j).1.slope → c.time≤(evaluate j).1.crossing := by
  have hb := scan_best evaluate rows
  rw [hc] at hb
  obtain ⟨j,hj,hPossible⟩ := hb.1
  have he := hPossible.1
  refine ⟨by rwa [he],?_,?_,?_⟩
  · rw [he]
    exact hPossible.2.1
  · rw [he]
    exact hPossible.2.2
  · intro k hk hp
    exact hb.2 ⟨k,(evaluate k).1.crossing⟩ ⟨k,hk,rfl,rfl,hp⟩

theorem exists_selected {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i)
    (j : i) (hj : j∈rows) (hp : 0<(evaluate j).1.slope) : ∃ c,(scan evaluate rows).choice=some c := by
  have hb := scan_best evaluate rows
  cases hc : (scan evaluate rows).choice with
  | none =>
    rw [hc] at hb
    exact (hb ⟨j,(evaluate j).1.crossing⟩ ⟨j,hj,rfl,rfl,hp⟩).elim
  | some c => exact ⟨c,rfl⟩

theorem endpoint_nonnegative {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i)
    (hStart : ∀ j∈rows,(evaluate j).1.intercept≤0) (c : Choice i) (hc : (scan evaluate rows).choice=some c) :
    0≤c.time := by
  have hs := selected evaluate rows c hc
  rw [hs.2.1]
  exact crossing_nonnegative _ (hStart _ hs.1) hs.2.2.1

theorem endpoint_tight {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i)
    (c : Choice i) (hc : (scan evaluate rows).choice=some c) :
    (evaluate c.blocker).1.value c.time=0 := by
  have hs := selected evaluate rows c hc
  rw [hs.2.1]
  exact crossing_tight _ hs.2.2.1

theorem forward_feasible {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i)
    (hStart : ∀ j∈rows,(evaluate j).1.intercept≤0) (c : Choice i) (hc : (scan evaluate rows).choice=some c)
    (t : ℚ) (ht : 0≤t ∧ t≤c.time) (j : i) (hj : j∈rows) : (evaluate j).1.value t≤0 := by
  by_cases hp : 0<(evaluate j).1.slope
  · apply (positive_iff _ hp t).mpr
    exact ht.2.trans ((selected evaluate rows c hc).2.2.2 j hj hp)
  · exact nonpositive_forward _ (hStart j hj) (le_of_not_gt hp) t ht.1

theorem beyond_infeasible {i : Type*} (evaluate : i → Affine × ℕ) (rows : List i)
    (c : Choice i) (hc : (scan evaluate rows).choice=some c) (t : ℚ) (ht : c.time<t) :
    0<(evaluate c.blocker).1.value t := by
  have hs := selected evaluate rows c hc
  apply beyond_crossing _ hs.2.2.1 t
  rwa [←hs.2.1]

end Blotto.GeneralPaperRayMinimumSound
