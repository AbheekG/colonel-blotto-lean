import Blotto.PlayerSpecificAlgebraicZeroExecution

/-! Executing reduced addition/subtraction, including the actual dense
operation, remainder division and complete input/returned/control copies. -/
namespace Blotto.PlayerSpecificFieldCombination
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

def raw (difference : Bool) (a b : Data) : Data×Trace :=
  if difference then PlayerSpecificDenseExecution.subtract a b else PlayerSpecificDenseExecution.add a b
def run (difference : Bool) (m a b : Data) : Data×Trace :=
  let combined:=raw difference a b
  let divided:=PlayerSpecificDivisionExecution.run combined.1 m
  let result:=divided.1.2
  (result,combined.2++divided.2++copyRow m++copyRow a++copyRow b++copyRow result++[.control 3])

theorem value (difference : Bool) (m a b : Data) :
    (run difference m a b).1=if difference then PlayerSpecificAlgebraicField.minus m a b else PlayerSpecificAlgebraicField.plus m a b := by
  cases difference <;> simp only [run,raw,Bool.false_eq_true,ite_false,ite_true,
    PlayerSpecificDivisionExecution.value,PlayerSpecificDenseExecution.add_value,
    PlayerSpecificDenseExecution.subtract_value,PlayerSpecificAlgebraicField.plus,
    PlayerSpecificAlgebraicField.minus,reduce]

theorem raw_bounds (difference : Bool) (a b : Data) (H : ℕ) (ha : HasHeight a H) (hb : HasHeight b H)
    (hal : a.length≤3) (hbl : b.length≤3) :
    HasHeight (raw difference a b).1 (2*H+1) ∧ (raw difference a b).1.length≤4 := by
  cases difference
  · simp only [raw,Bool.false_eq_true,ite_false,PlayerSpecificDenseExecution.add_value]
    exact ⟨by simpa only [two_mul] using add_height ha hb,by rw [add_length]; omega⟩
  · simp only [raw,ite_true,PlayerSpecificDenseExecution.subtract_value]
    exact ⟨by simpa only [two_mul] using subtract_height ha hb,by rw [subtract,add_length,scale_length]; omega⟩

theorem reduced (difference : Bool) (m a b : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (run difference m a b).1 := by
  change Reduced m (PlayerSpecificDivisionExecution.run (raw difference a b).1 m).1.2
  rw [PlayerSpecificDivisionExecution.value]
  exact PlayerSpecificAlgebraicReduction.reduced m _ hm hm0

theorem bounds (difference : Bool) (m a b : Data) (H : ℕ)
    (hm : HasHeight m H) (ha : HasHeight a H) (hb : HasHeight b H)
    (hml : m.length≤4) (hal : a.length≤3) (hbl : b.length≤3) :
    HasHeight (run difference m a b).1 (100000*(H+1)) := by
  have hr:=raw_bounds difference a b H ha hb hal hbl
  have hd:=PlayerSpecificDivisionExecution.heights (raw difference a b).1 m (2*H+1) hr.1
    (mono hm (by omega)) (by omega) hr.2 hml
  exact mono hd.2 (by omega)

theorem real_value (difference : Bool) (m a b : Data) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate (run difference m a b).1 x=
      if difference then realEvaluate a x-realEvaluate b x else realEvaluate a x+realEvaluate b x := by
  rw [value]
  cases difference <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    PlayerSpecificAlgebraicField.minus_value m a b x hx,PlayerSpecificAlgebraicField.plus_value m a b x hx]

end Blotto.PlayerSpecificFieldCombination
