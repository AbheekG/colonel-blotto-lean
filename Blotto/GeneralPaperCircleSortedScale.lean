import Blotto.GeneralPaperNativeSortedModels

/-! Common positive budget scaling commutes with sorted-row circle
reconstruction. Unit rational rows can be sorted/stored before applying
the original budget scale, avoiding long-budget sorting comparisons. -/
namespace Blotto.GeneralPaperCircleSortedScale
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sorted_scale {R : ℕ} (x : Fin R → ℝ) (c : ℝ) (hc : 0<c) (a : Fin R) :
    GeneralPaperCircleSortedComparison.sorted (fun j => c*x j) a=
      c*GeneralPaperCircleSortedComparison.sorted x a := by
  have hm : Monotone ((fun j => c*x j) ∘ Tuple.sort x) :=
    fun i j hij => mul_le_mul_of_nonneg_left (GeneralPaperCircleSortedComparison.sorted_monotone x hij) hc.le
  have he := (Tuple.comp_sort_eq_comp_iff_monotone (f:=fun j => c*x j) (σ:=Tuple.sort x)).mpr hm
  exact (congrFun he a).symm

theorem bid_scale {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Fin R → ℝ) (c : ℝ) (shift : ℕ) (j : Fin g) :
    GeneralPaperCircleHardBudget.bid R W hR hW weights (fun a => c*x a) shift j=
      c*GeneralPaperCircleHardBudget.bid R W hR hW weights x shift j := by
  unfold GeneralPaperCircleHardBudget.bid
  ring

theorem reconstructed_scale {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (kept : Allocation h) (x : Fin R → ℝ) (c : ℝ) (hc : 0<c) (shift : ℕ) :
    GeneralPaperCircleHardBudget.reconstruct R W hR hW weights (scaleAllocation c kept)
      (GeneralPaperCircleSortedComparison.sorted (fun a => c*x a)) shift=
      scaleAllocation c (GeneralPaperCircleHardBudget.reconstruct R W hR hW weights kept
        (GeneralPaperCircleSortedComparison.sorted x) shift) := by
  have hs : GeneralPaperCircleSortedComparison.sorted (fun a => c*x a)=
      (fun a => c*GeneralPaperCircleSortedComparison.sorted x a) := funext (sorted_scale x c hc)
  rw [hs]
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro i
    simp only [GeneralPaperCircleHardBudget.reconstruct_kept,scaleAllocation]
  · intro i
    simp only [GeneralPaperCircleHardBudget.reconstruct_light,scaleAllocation,bid_scale]

end Blotto.GeneralPaperCircleSortedScale
