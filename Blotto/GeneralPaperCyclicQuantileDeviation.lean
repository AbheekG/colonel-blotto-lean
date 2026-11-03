import Blotto.GeneralPaperWeightedLowerQuantile

/-! Fixed named cyclic deviations from weighted uniform lower quantiles.
The construction takes only the original deviation and field weights: no
defender row is an argument. Every cyclic deviation has the hard budget. -/
namespace Blotto.GeneralPaperCyclicQuantileDeviation
open GeneralPaperCircleCell GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def representative (R : ℕ) (hR : 0<R) (q : Fin R → ℝ) (s : ℕ) : Allocation R :=
  fun a => q (cell R hR a.val s)/(R:ℝ)

noncomputable def row {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (kept : Allocation h) (y : Fin g → ℝ) (s : ℕ) : Allocation (h+R) :=
  Fin.addCases kept (representative R hR (GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y) s)

theorem representative_sum (R : ℕ) (hR : 0<R) (q : Fin R → ℝ) (s : ℕ) :
    (∑ a,representative R hR q s a)=average q := by
  have he : ∀ a:Fin R,cell R hR a.val s=cell R hR s a.val := by
    intro a
    apply Fin.ext
    exact congrArg (fun t => t%R) (Nat.add_comm a.val s)
  unfold representative average
  rw [←Finset.sum_div]
  simp_rw [he]
  rw [GeneralPaperCircleFiniteSums.rotation R hR s q]

theorem kept_read {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (kept : Allocation h) (y : Fin g → ℝ) (s : ℕ) (j : Fin h) :
    row R W hR hW weights hs kept y s (Fin.castAdd R j)=kept j := by simp only [row,Fin.addCases_left]

theorem representative_read {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (kept : Allocation h) (y : Fin g → ℝ) (s : ℕ) (a : Fin R) :
    row R W hR hW weights hs kept y s (Fin.natAdd h a)=
      GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y (cell R hR a.val s)/(R:ℝ) := by
  simp only [row,Fin.addCases_right,representative]

theorem feasible {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W) (kept : Allocation h) (y : Fin g → ℝ)
    (B : ℝ) (hOriginal : Feasible B (Fin.addCases kept y)) (s : ℕ) :
    Feasible B (row R W hR hW weights hs kept y s) := by
  have hy : ∀ j,0≤y j := fun j => by simpa only [Fin.addCases_right] using hOriginal.1 (Fin.natAdd h j)
  have hk : ∀ j,0≤kept j := fun j => by simpa only [Fin.addCases_left] using hOriginal.1 (Fin.castAdd g j)
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro a
      simpa only [kept_read] using hk a
    · intro a
      rw [representative_read]
      exact div_nonneg (GeneralPaperWeightedLowerQuantile.nonnegative R W hR hW weights hs y hy _) (Nat.cast_nonneg R)
  · rw [Fin.sum_univ_add]
    simp only [kept_read,representative_read]
    change (∑ j,kept j)+(∑ a,representative R hR (GeneralPaperWeightedLowerQuantile.quantiles R W hR hW weights hs y) s a)≤B
    rw [representative_sum]
    have hb := hOriginal.2
    rw [Fin.sum_univ_add] at hb
    simp only [Fin.addCases_left,Fin.addCases_right] at hb
    have hm := GeneralPaperWeightedLowerQuantile.mean_bound R W hR hW weights hp hs y hy
    linarith only [hb,hm]

theorem share_scaled (R : ℕ) (hR : 0<R) (q x : ℝ) : share (q/(R:ℝ)) x=share q ((R:ℝ)*x) := by
  have hr : (0:ℝ)<R := by exact_mod_cast hR
  have h := share_scale hr (q/(R:ℝ)) x
  rw [mul_div_cancel₀ _ hr.ne'] at h
  exact h.symm

theorem payoff_average (R : ℕ) (hR : 0<R) (q x : Fin R → ℝ) (V : ℝ) :
    average (fun s:Fin R => ∑ a,(V/(R:ℝ))*share (representative R hR q s.val a) (x a))=
      (V/(R:ℝ))*∑ a,average (fun l => share (q l) ((R:ℝ)*x a)) := by
  rw [average_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [average_mul]
  congr 1
  unfold representative
  simp_rw [share_scaled R hR]
  exact average_rotation R hR a.val (fun l => share (q l) ((R:ℝ)*x a))

end Blotto.GeneralPaperCyclicQuantileDeviation
