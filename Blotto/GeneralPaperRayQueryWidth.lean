import Blotto.GeneralPaperRayMinimumBits

/-! The common-lattice DP word envelope fits the already established root
envelope plus probe height. This prevents an extra factor of m in the actual
bit price of every fixed-probe query.
-/
namespace Blotto.GeneralPaperRayQueryWidth
open GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem width {m D E X V P s : ℕ} (t : ℚ) (ht : RationalHeight t s) :
    GeneralPaperCommonLatticeDPBits.width (D*t.den) (X+V+1) m≤
      1+2*(GeneralPaperRayUniformSize.width D E m X V P+s) := by
  let A := interceptCap m X P
  let B := slopeCap m V
  have hCap : (m+1)*(X+V+1)+1≤A+1+B := by
    unfold A B interceptCap slopeCap
    nlinarith only [Nat.zero_le ((m+1)*P)]
  have hM := binaryWordWidth_mono hCap
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add (A+1) B
  have hA := binaryWordWidth_mono (show A+1≤A+A+1 by omega)
  have hB := binaryWordWidth_mono (show B≤B+B+1 by omega)
  have hE := binaryWordWidth_pos E
  have hPeriod := binaryWordWidth_mul D t.den
  have hDen := binaryWordWidth_le_of_lt_pow ht.positive ht.2
  change 1+2*(binaryWordWidth ((m+1)*(X+V+1)+1)+binaryWordWidth (D*t.den))≤
    1+2*(binaryWordWidth (A+A+1)+binaryWordWidth D+binaryWordWidth (B+B+1)+binaryWordWidth E+s)
  omega

end Blotto.GeneralPaperRayQueryWidth
