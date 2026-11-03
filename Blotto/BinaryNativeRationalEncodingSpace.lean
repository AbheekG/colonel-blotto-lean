import Blotto.BinaryBalancedWordEncodingSpace
import Blotto.BinaryNativeRationalEncoder
import Blotto.RationalPRGStoredOutput

/-! Sequential numerator/denominator encoding retains the input rational
once, plus the active numeric encoder's stack. Boolean payload/output cells,
address/header records and primitive-internal workspace are separate layers. -/

namespace Blotto.BinaryNativeRationalEncodingSpace
open BinaryBalancedWordEncodingSpace
set_option autoImplicit false

def numericPeak (q : ℚ) : ℕ :=
  rationalWordWidth q+4+max (bitsPeak q.num.natAbs) (bitsPeak q.den)

theorem numeric_peak_bound (q : ℚ) : numericPeak q ≤ 49*rationalWordWidth q+28 := by
  have hn := bits_peak_bound q.num.natAbs
  have hd := bits_peak_bound q.den
  have hwN : binaryWordWidth q.num.natAbs ≤ rationalWordWidth q := by unfold rationalWordWidth; omega
  have hwD : binaryWordWidth q.den ≤ rationalWordWidth q := by unfold rationalWordWidth; omega
  have hm : max (bitsPeak q.num.natAbs) (bitsPeak q.den) ≤ 48*rationalWordWidth q+24 :=
    max_le (by omega) (by omega)
  unfold numericPeak
  omega

theorem actual_word_and_numeric_peak (q : ℚ) :
    BinaryRationalNormalization.value (BinaryNativeRationalEncoder.word q) = q ∧
      numericPeak q ≤ 49*rationalWordWidth q+28 :=
  ⟨BinaryNativeRationalEncoder.word_value q,numeric_peak_bound q⟩

theorem every_actual_numeric_path (q : ℚ) (retained : ℕ)
    (path : RetainedPath (binaryWordWidth q.num.natAbs) q.num.natAbs retained ∨
      RetainedPath (binaryWordWidth q.den) q.den retained) :
    rationalWordWidth q+4+retained ≤ 49*rationalWordWidth q+28 := by
  have hp : retained ≤ max (bitsPeak q.num.natAbs) (bitsPeak q.den) := by
    rcases path with hn | hd
    · exact (retained_path_le_peak hn).trans (le_max_left _ _)
    · exact (retained_path_le_peak hd).trans (le_max_right _ _)
  have hb := numeric_peak_bound q
  unfold numericPeak at hb
  omega

end Blotto.BinaryNativeRationalEncodingSpace

namespace Blotto.RationalPRGOriginalInput

theorem stored_encoder_numeric_peaks {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    BinaryNativeRationalEncodingSpace.numericPeak ((i.storedRichSample K bits).allocation j) ≤
      49*(2^77*(i.originalInputWordWidth+K+6))+28 ∧
    BinaryNativeRationalEncodingSpace.numericPeak ((i.storedPoorSample K bits).allocation j) ≤
      49*(2^77*(i.originalInputWordWidth+K+6))+28 := by
  have hw := i.storedSample_widths K bits j
  have hr := BinaryNativeRationalEncodingSpace.numeric_peak_bound ((i.storedRichSample K bits).allocation j)
  have hp := BinaryNativeRationalEncodingSpace.numeric_peak_bound ((i.storedPoorSample K bits).allocation j)
  constructor <;> omega

end Blotto.RationalPRGOriginalInput
