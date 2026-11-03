import Blotto.GeneralPaperEqualCompactedSampler
import Blotto.GeneralPaperPowerCeilingBits

/-! Discover the rejection width by actual doubling of a stored denominator.
The existing measured power-ceiling routine computes its exponent once;
neither a logarithm oracle nor the mathematical segment count is executed. -/
namespace Blotto.GeneralPaperStoredRejectionWidth
set_option autoImplicit false

def run (model : RationalCostModel) (A D : ℕ) : ℕ × ℕ :=
  let actual := GeneralPaperPowerCeilingBits.run model.rat A D
  (actual.1.doublings, actual.2 + 64 * A + 64)

theorem data (model : RationalCostModel) (A D : ℕ) (hD : 0 < D) :
    (run model A D).1 = UniformNatRejection.width D := by
  unfold run
  dsimp only
  rw [GeneralPaperPowerCeilingBits.data]
  apply Nat.le_antisymm
  · exact GeneralPaperPowerCeiling.ceiling_minimal D _ (UniformNatRejection.width_upper D)
  · apply widthRatioPrecision_minimal D 1 _ hD (by decide)
    simpa only [one_mul, GeneralPaperPowerCeiling.ceiling_power] using
      GeneralPaperPowerCeiling.ceiling_lower D

theorem work (model : RationalCostModel) (A D : ℕ) :
    (run model A D).2 ≤
      64 * (binaryWordWidth D + 1) * (A + model.rat (1 + binaryWordWidth (2 * (D + 1)))) + 64 * A + 64 := by
  have h := GeneralPaperPowerCeilingBits.work model.rat model.monotone A D
  exact Nat.add_le_add_right (Nat.add_le_add_right h (64 * A)) 64

theorem word_work (model : RationalCostModel) (A D L : ℕ) (hD : binaryWordWidth D ≤ L) :
    (run model A D).2 ≤ 128 * (L + 1) * (A + model.rat (L + 6) + 1) := by
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add D 1
  have hMul := binaryWordWidth_mul 2 (D + 1)
  have h1 : binaryWordWidth 1 = 1 := by decide
  have h2 : binaryWordWidth 2 = 2 := by decide
  have hRat := model.monotone (show 1 + binaryWordWidth (2 * (D + 1)) ≤ L + 6 by omega)
  have hW := work model A D
  have hScale := Nat.mul_le_mul (show binaryWordWidth D + 1 ≤ L + 1 by omega)
    (show A + model.rat (1 + binaryWordWidth (2 * (D + 1))) ≤ A + model.rat (L + 6) by omega)
  nlinarith only [hW, hScale]

end Blotto.GeneralPaperStoredRejectionWidth
