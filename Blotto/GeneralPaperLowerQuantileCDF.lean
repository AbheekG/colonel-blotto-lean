import Blotto.GeneralPaperQuantileRankCount

/-! Both CDF conventions of the uniform lower-quantile comparison, with
canonical half ties and q_0=0. Only nonnegative original bids are assumed;
the support need not be bounded by one or have rational coordinates. -/
namespace Blotto.GeneralPaperLowerQuantileCDF
open GeneralPaperLowerQuantile GeneralPaperCircleThresholdRank GeneralPaperCircleFiniteAverage
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem strict_nonpositive {N : ℕ} (Y : Fin N → ℝ) (hY : ∀ i,0≤Y i) (t : ℝ) (ht : t≤0) : strict Y t=0 := by
  unfold strict
  rw [Finset.filter_eq_empty_iff.mpr (fun i _ => not_lt_of_ge (ht.trans (hY i))),Finset.card_empty]

theorem weak_negative {N : ℕ} (Y : Fin N → ℝ) (hY : ∀ i,0≤Y i) (t : ℝ) (ht : t<0) : weak Y t=0 := by
  unfold weak
  rw [Finset.filter_eq_empty_iff.mpr (fun i _ => not_le_of_gt (ht.trans_le (hY i))),Finset.card_empty]

theorem strict_rank (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (t : ℝ) (ht : 0<t) :
    strict (row R W hR hW Y) t=GeneralPaperQuantileRankCount.count R W (strict Y t) := by
  unfold strict GeneralPaperQuantileRankCount.count
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact strict_test R W hR hW Y hY t ht a

theorem weak_rank (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (t : ℝ) (ht : 0≤t) :
    weak (row R W hR hW Y) t=GeneralPaperQuantileRankCount.count R W (weak Y t) := by
  unfold weak GeneralPaperQuantileRankCount.count
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact weak_test R W hR hW Y hY t ht a

theorem strict_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (h0 : ∀ i,0≤Y i) (t : ℝ) :
    0≤(strict (row R W hR hW Y) t:ℝ)/R-(strict Y t:ℝ)/W ∧
      (strict (row R W hR hW Y) t:ℝ)/R-(strict Y t:ℝ)/W≤1/(R:ℝ) := by
  by_cases ht : 0<t
  · rw [strict_rank R W hR hW Y hY t ht]
    exact GeneralPaperQuantileRankCount.probability_bounds R W (strict Y t) hR hW (strict_le Y t)
  · have ht' := le_of_not_gt ht
    rw [strict_nonpositive (row R W hR hW Y) (nonnegative R W hR hW Y h0) t ht',strict_nonpositive Y h0 t ht']
    simp only [Nat.cast_zero,zero_div,sub_self,le_refl,true_and]
    positivity

theorem weak_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (h0 : ∀ i,0≤Y i) (t : ℝ) :
    0≤(weak (row R W hR hW Y) t:ℝ)/R-(weak Y t:ℝ)/W ∧
      (weak (row R W hR hW Y) t:ℝ)/R-(weak Y t:ℝ)/W≤1/(R:ℝ) := by
  by_cases ht : 0≤t
  · rw [weak_rank R W hR hW Y hY t ht]
    exact GeneralPaperQuantileRankCount.probability_bounds R W (weak Y t) hR hW (weak_le Y t)
  · have ht' := lt_of_not_ge ht
    rw [weak_negative (row R W hR hW Y) (nonnegative R W hR hW Y h0) t ht',weak_negative Y h0 t ht']
    simp only [Nat.cast_zero,zero_div,sub_self,le_refl,true_and]
    positivity

theorem law_cdf_close (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (h0 : ∀ i,0≤Y i) :
    RealCDFClose (finiteUniformPoints hW Y) (finiteUniformPoints hR (row R W hR hW Y)) (1/(R:ℝ)) := by
  intro t
  rw [law_weak,law_weak]
  have h := weak_error R W hR hW Y hY h0 t
  apply abs_le.mpr
  constructor <;> linarith only [h.1,h.2]

theorem opponent_share_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (h0 : ∀ i,0≤Y i) (t : ℝ) :
    0≤average (fun a => share t (row R W hR hW Y a))-average (fun i => share t (Y i)) ∧
      average (fun a => share t (row R W hR hW Y a))-average (fun i => share t (Y i))≤1/(R:ℝ) := by
  rw [average_share,average_share]
  have hs := strict_error R W hR hW Y hY h0 t
  have hw := weak_error R W hR hW Y hY h0 t
  constructor <;> linarith only [hs.1,hs.2,hw.1,hw.2]

theorem share_average_sum {N : ℕ} (hN : 0<N) (Y : Fin N → ℝ) (t : ℝ) :
    average (fun i => share (Y i) t)+average (fun i => share t (Y i))=1 := by
  unfold GeneralPaperCircleFiniteAverage.average
  rw [←add_div,←Finset.sum_add_distrib]
  simp only [share_constant_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast hN.ne')

theorem attacker_share_error (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ) (hY : Monotone Y) (h0 : ∀ i,0≤Y i) (t : ℝ) :
    0≤average (fun i => share (Y i) t)-average (fun a => share (row R W hR hW Y a) t) ∧
      average (fun i => share (Y i) t)-average (fun a => share (row R W hR hW Y a) t)≤1/(R:ℝ) := by
  have h := opponent_share_error R W hR hW Y hY h0 t
  have hY' := share_average_sum hW Y t
  have hQ' := share_average_sum hR (row R W hR hW Y) t
  constructor <;> linarith only [h.1,h.2,hY',hQ']

end Blotto.GeneralPaperLowerQuantileCDF
