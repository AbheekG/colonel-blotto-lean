import Blotto.GeneralPaperSharedSpanPrice

/-! The quantile-comparison width is computed from retained precision.
No precision, power-table or source-constant constructor is replayed.
-/
namespace Blotto.GeneralPaperSharedWidthPrice
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (p k : ℕ) : ℕ := 64+8*(binaryWordWidth p+binaryWordWidth k+1)

def work (primitive : ℕ → ℕ) (p k : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) 34 k+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) p 1+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (p+1) (34+k)

theorem work_le (primitive : ℕ → ℕ) (hMono : Monotone primitive) (p k : ℕ) :
    work primitive p k≤6*primitive (width p k) := by
  have hK := GeneralPaperRayOperandWidthEnvelope.word_add 34 k
  have hP := GeneralPaperRayOperandWidthEnvelope.word_add p 1
  have hSum := GeneralPaperRayOperandWidthEnvelope.word_add (p+1) (34+k)
  have h34 : binaryWordWidth 34=6 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have hk := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) 34 k (width p k)
    (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  have hp := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) p 1 (width p k)
    (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  have hs := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (p+1) (34+k) (width p k)
    (by unfold width; omega) (by unfold width; omega) (by unfold width; omega)
  unfold work
  omega

theorem operand_width (m lambda k Qv : ℕ) :
    width (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits k≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hp := (GeneralPaperSourcePreparationControls.metadata m lambda k Qv).fractionalBits
  have hpw := GeneralPaperInitializerControlCounters.word_le_self (GeneralPaperPowerPrecision.prepare lambda k).fractionalBits
  have hkw := GeneralPaperInitializerControlCounters.word_le_self k
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hm := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  unfold width GeneralPaperPowerPreparationEnvelope.operandWidth
  omega

end Blotto.GeneralPaperSharedWidthPrice
