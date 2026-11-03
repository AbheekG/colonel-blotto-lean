import Blotto.GeneralPaperInitialForestPrice

/-! Centering a normalized exponent at the mantissa precision removes p
from the multiplication recurrence. This is an analytical invariant only;
the stored representation and its arithmetic are unchanged.
-/
namespace Blotto.GeneralPaperCenteredExponent
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def centered (p : ℕ) (x : Number) : ℤ := x.exponent+(p:ℤ)
def Power (p degree : ℕ) (x : Number) : Prop := -(degree:ℤ)≤centered p x ∧ centered p x≤-1

theorem multiply (unit p : ℕ) (left right : Number) (hl : 0<left.mantissa) (hr : 0<right.mantissa) :
    centered p left+centered p right≤centered p (GeneralPaperDyadicMultiply.multiply unit p left right).number ∧
      centered p (GeneralPaperDyadicMultiply.multiply unit p left right).number≤centered p left+centered p right+1 := by
  have hNonzero : ¬(left.mantissa=0 ∨ right.mantissa=0) := by omega
  simp only [centered,GeneralPaperDyadicMultiply.multiply,hNonzero,ite_false]
  unfold GeneralPaperDyadicMultiply.shift
  split <;> push_cast <;> omega

theorem power_multiply (unit p dl dr : ℕ) (left right : Number) (hl : 0<left.mantissa) (hr : 0<right.mantissa)
    (hLeft : Power p dl left) (hRight : Power p dr right) :
    Power p (dl+dr) (GeneralPaperDyadicMultiply.multiply unit p left right).number := by
  have h := multiply unit p left right hl hr
  unfold Power at *
  push_cast
  omega

theorem stored_base (unit p k : ℕ) :
    centered p (GeneralPaperStoredGeometricBase.construct unit p k).number=-1 := by
  simp only [centered,GeneralPaperStoredGeometricBase.construct]
  push_cast
  omega

theorem absolute_bound (p degree : ℕ) (x : Number)
    (hLower : -(degree:ℤ)≤centered p x) (hUpper : centered p x≤0) : x.exponent.natAbs≤degree+p := by
  unfold centered at hLower hUpper
  omega

end Blotto.GeneralPaperCenteredExponent
