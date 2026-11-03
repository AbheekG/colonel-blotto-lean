import Blotto.PlayerSpecificRationalIntervalsCopyCost

/-! Complete actual finite-bit interval preparation, including original
input tables, stable ratio sort, field materialization, one-time sweep and
all enclosing copies. The same cell list has polynomial input sizes/cost. -/
namespace Blotto.PlayerSpecificRationalIntervalsContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificRationalIntervalsExecution PlayerSpecificRationalIntervalsCopyCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total_profile (N R sorted sweep frame : ℕ) (hs : sorted≤5000000*(N+1)^3*R)
    (hw : sweep≤20000*(N+2)^2*R) (hf : frame≤1000*(N+2)*R) :
    sorted+sweep+frame≤10000000*(N+1)^3*R := by
  have hsquare : (N+2)^2≤4*(N+1)^3 := by nlinarith only [Nat.zero_le (N^3),Nat.zero_le (N^2)]
  have hlinear : N+2≤2*(N+1)^3 := by nlinarith only [Nat.zero_le (N^3),Nat.zero_le (N^2)]
  have hsp:=Nat.mul_le_mul_right (20000*R) hsquare
  have hlp:=Nat.mul_le_mul_right (1000*R) hlinear
  have hr : 0≤(N+1)^3*R := Nat.zero_le _
  nlinarith only [hs,hw,hf,hsp,hlp,hr]

theorem source_cost {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    (run model i).2≤10000000*(N+1)^3*model.rat (width N (inputSize i)) := by
  have hs:=PlayerSpecificSortedFieldsContract.source_cost model i
  have hsp:=hs.trans (Nat.mul_le_mul_left _ (model.monotone (widths N (inputSize i)).1))
  have hh:=PlayerSpecificSortedFieldsExecution.heights model i
  have hw:=PlayerSpecificSweepPreparationContract.source_cost model (PlayerSpecificSortedFieldsExecution.run model i).1
    (inputSize i) hh (PlayerSpecificRecognitionInputHeights.input_positive i)
  rw [PlayerSpecificSortedFieldsExecution.length] at hw
  have hf:=frame_cost model i
  simp only [PlayerSpecificRationalIntervalsExecution.run] at hf ⊢
  exact total_profile N _ _ _ _ hsp hw hf

theorem actual_contract {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    let result:=run model i
    result.1=PlayerSpecificRationalIntervals.run i ∧ result.1.length=N+1 ∧
      (∀ c∈result.1,PlayerSpecificRationalCellHeights.CellHeight c (height N (inputSize i))) ∧
      (∀ c∈result.1,semantics (cubic c.state.coefficients i.budget)≠0) ∧
      result.2≤10000000*(N+1)^3*model.rat (width N (inputSize i)) := by
  refine ⟨value model i,length model i,heights model i,?_,source_cost model i⟩
  rw [value]
  exact PlayerSpecificRationalIntervals.cubic_nonzero i

theorem schoolbook_profile (N L : ℕ) :
    10000000*(N+1)^3*RationalCostModel.schoolbook.rat (width N L)≤
      (10000000*(4096*4096+4096))*(N+1)^3*((N+1)*(L+1))^2 := by
  have hp:=PlayerSpecificAlgebraicInverseContract.quadratic_profile 10000000 4096 ((N+1)*(L+1)) (by
    have hm:=Nat.mul_le_mul (show 1≤N+1 by omega) (show 1≤L+1 by omega)
    simpa only [Nat.one_mul] using hm)
  have hm:=Nat.mul_le_mul_left ((N+1)^3) hp
  dsimp only [width,PlayerSpecificSweepPreparationBudget.width,RationalCostModel.schoolbook]
  ring_nf at hm ⊢
  exact hm

theorem polynomial_cost {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run RationalCostModel.schoolbook i).2≤
      (10000000*(4096*4096+4096))*(N+1)^3*((N+1)*(inputSize i+1))^2 :=
  (source_cost RationalCostModel.schoolbook i).trans (schoolbook_profile N (inputSize i))

end Blotto.PlayerSpecificRationalIntervalsContract
