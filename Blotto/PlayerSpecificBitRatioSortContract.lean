import Blotto.PlayerSpecificBitRatioSortCost

/-! The bit-priced ratio sort returns the exact preserved stable field
order. Its complete operand/index/control source cost is polynomial in
the original rational row height and length. -/
namespace Blotto.PlayerSpecificBitRatioSortContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificBitRatioSortExecution PlayerSpecificBitRatioSortBudget
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_contract {N : ℕ} (model : RationalCostModel) (H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) :
    let result:=run model v w
    result.1=(PlayerSpecificRatioSort.run v w).1 ∧ Function.Bijective result.1.read ∧
      Monotone (fun j => v.read (result.1.read j)/w.read (result.1.read j)) ∧
      result.2≤2000000*(N+1)^3*model.rat (width N H) := by
  have hdata:=value model v w
  refine ⟨hdata,?_,?_,PlayerSpecificBitRatioSortCost.source_cost model H v w hv hw⟩
  · rw [hdata]; exact PlayerSpecificRatioSort.bijective v w
  · rw [hdata]; exact PlayerSpecificRatioSort.ordered v w

theorem polynomial_cost {N : ℕ} (H : ℕ) (v w : FixedArrayTable N ℚ)
    (hv : ∀ j,RationalHeight (v.read j) H) (hw : ∀ j,RationalHeight (w.read j) H) :
    (run RationalCostModel.schoolbook v w).2≤
      (2000000*(128*128+128))*(N+1)^3*(N+H+1)^2 := by
  have hc:=PlayerSpecificBitRatioSortCost.source_cost RationalCostModel.schoolbook H v w hv hw
  have hp:=PlayerSpecificAlgebraicInverseContract.quadratic_profile 2000000 128 (N+H+1) (by omega)
  have hm:=Nat.mul_le_mul_left ((N+1)^3) hp
  change (run RationalCostModel.schoolbook v w).2≤2000000*(N+1)^3*((128*(N+H+1))*(128*(N+H+1))+128*(N+H+1)) at hc
  apply hc.trans
  convert hm using 1 <;> ring

end Blotto.PlayerSpecificBitRatioSortContract
