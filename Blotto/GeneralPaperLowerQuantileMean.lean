import Blotto.GeneralPaperLowerQuantileCDF

/-! The uniform lower-quantile mean is no larger than the original mean.
A finite common-grid domination proves the lower Riemann-sum assertion
without any integration or mean/budget oracle. The grid is erased analysis. -/
namespace Blotto.GeneralPaperLowerQuantileMean
open GeneralPaperLowerQuantile GeneralPaperCircleCell GeneralPaperCircleFiniteSums GeneralPaperCircleFiniteAverage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem cell_bound (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ)
    (hY : Monotone Y) (h0 : ∀ i,0≤Y i) (c : Fin (R*W)) :
    row R W hR hW Y (bin R W hW c)≤Y (bin W R hR (Fin.cast (Nat.mul_comm R W) c)) := by
  unfold row
  split_ifs
  · exact h0 _
  · apply hY
    change ((c.val/W*W-1)/R)≤c.val/R
    exact Nat.div_le_div_right ((Nat.sub_le _ 1).trans (Nat.div_mul_le_self c.val W))

theorem transposed_bins (R W : ℕ) (hR : 0<R) (Y : Fin W → ℝ) :
    (∑ c:Fin (R*W),Y (bin W R hR (Fin.cast (Nat.mul_comm R W) c)))=(R:ℝ)*∑ i,Y i := by
  have h := Equiv.sum_comp (finCongr (Nat.mul_comm R W)) (fun c:Fin (W*R) => Y (bin W R hR c))
  exact h.trans (bins W R hR Y)

theorem sum_bound (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ)
    (hY : Monotone Y) (h0 : ∀ i,0≤Y i) :
    (W:ℝ)*(∑ a,row R W hR hW Y a)≤(R:ℝ)*∑ i,Y i := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => cell_bound R W hR hW Y hY h0 c)
  rw [bins R W hW (row R W hR hW Y),transposed_bins R W hR Y] at h
  exact h

theorem mean_bound (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ)
    (hY : Monotone Y) (h0 : ∀ i,0≤Y i) : average (row R W hR hW Y)≤average Y := by
  have h := sum_bound R W hR hW Y hY h0
  apply (div_le_div_iff₀ (by exact_mod_cast hR : (0:ℝ)<R) (by exact_mod_cast hW : (0:ℝ)<W)).mpr
  nlinarith only [h]

theorem feasible (R W : ℕ) (hR : 0<R) (hW : 0<W) (Y : Fin W → ℝ)
    (hY : Monotone Y) (h0 : ∀ i,0≤Y i) :
    Feasible (average Y) (fun a => row R W hR hW Y a/(R:ℝ)) := by
  constructor
  · intro a
    exact div_nonneg (GeneralPaperLowerQuantile.nonnegative R W hR hW Y h0 a) (Nat.cast_nonneg R)
  · rw [←Finset.sum_div]
    exact mean_bound R W hR hW Y hY h0

end Blotto.GeneralPaperLowerQuantileMean
