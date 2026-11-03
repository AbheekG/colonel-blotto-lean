import Blotto.BinaryNormalizationPlan

/-! Actual terminal/physical arithmetic uses the planned normalization producer.
Both preceding measured interfaces are exact projections of its single returned
record. Division/emission extras retain separate prices and need caller joins. -/
namespace Blotto.BinaryPlannedQuadratic
open BinaryRationalNormalization BinarySeedPreparationSpace
set_option autoImplicit false

def applyMeasured (op : RealArithmeticOp) (first second : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  (BinaryNormalizationPlan.apply op first second).1

theorem applyMeasured_previous (op : RealArithmeticOp) (first second : SignedWord) :
    applyMeasured op first second = BinaryQuadraticMeasured.applyMeasured op first second :=
  BinaryNormalizationPlan.apply_compat op first second

def apply (op : RealArithmeticOp) (first second : SignedWord) : (SignedWord × Trace) × ℕ :=
  (applyMeasured op first second).1

theorem apply_previous (op : RealArithmeticOp) (first second : SignedWord) :
    apply op first second = BinaryQuadraticMeasured.apply op first second := by
  simp only [apply,applyMeasured_previous,BinaryQuadraticMeasured.apply]

def extra (op : RealArithmeticOp) (first second : SignedWord) : ℕ :=
  let produced := BinaryNormalizationPlan.apply op first second
  produced.1.2+produced.2

theorem extra_bound (op : RealArithmeticOp) (first second : SignedWord) :
    extra op first second ≤ 4*(apply op first second).2+25*(apply op first second).1.2.length+5 := by
  have hd := BinaryNormalizationPlan.apply_division op first second
  have he := BinaryNormalizationPlan.apply_price op first second
  simp only [extra,apply,applyMeasured]
  omega

end Blotto.BinaryPlannedQuadratic
