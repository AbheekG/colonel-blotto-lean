import Blotto.GeneralPaperEqualOuterNativeContract

/-! Typed semantic values of the retained scalar cells. The schema fixes
the type of each owned cell, so these constructor annotations do not add a
per-cell encoded discriminator. Encoded sizes and measured singleton plans
are the existing natural/rational/Boolean primitives. -/
namespace Blotto.GeneralPaperRetainedScalarValue
open GeneralPaperMeasuredBlockPlan GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

inductive Scalar where
  | natural : ℕ → Scalar
  | rational : ℚ → Scalar
  | bit : Bool → Scalar

def encode : Scalar → ℕ
  | .natural value => natBits value
  | .rational value => rationalWordWidth value
  | .bit _ => 1

def measure (model : RationalCostModel) (S : ℕ) : Scalar → Plan
  | .natural value => natural model S value
  | .rational value => rational model S value
  | .bit value => GeneralPaperEqualMeasuredLeafPlans.bit S value

theorem measured (model : RationalCostModel) (S : ℕ) (value : Scalar) :
    (measure model S value).sizes = [encode value] := by
  cases value with
  | natural n => exact natural_data model S n
  | rational q => exact rational_data model S q
  | bit b => rfl

theorem positive (value : Scalar) : 0 < encode value := by
  cases value with
  | natural n => exact Nat.zero_lt_succ _
  | rational q => have h := GeneralPaperEqualNativeDrawRepresentation.budget_width q; exact lt_of_lt_of_le (by decide : 0 < 3) h
  | bit b => exact Nat.zero_lt_one

theorem natural_size (value : ℕ) : encode (.natural value) = natBits value := rfl

theorem rational_size (value : ℚ) : encode (.rational value) = rationalWordWidth value := rfl

theorem bit_size (value : Bool) : encode (.bit value) = 1 := rfl

end Blotto.GeneralPaperRetainedScalarValue
