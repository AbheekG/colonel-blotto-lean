import Blotto.GeneralPaperOriginalMeasuredReference

/-! Close the unequal producer from already selected accuracy. This actual
continuation neither rereads accuracy nor remeasures the reference. Its
return agrees with the established driver at the supplied reference words;
the work identity removes precisely the skipped accuracy pass and wrapper. -/
namespace Blotto.GeneralPaperClosedParsedPreparation
open GeneralPaperBinaryAccuracy (Parsed)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def run {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (parsed : Parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) : GeneralPaperClosedStrategyDriver.Prepared n × ℕ :=
  let raw := GeneralPaperAccuracyStrategyDriver.bitFromExponent model Wv Ws A parsed.exponent values v hv b hb
  let stored := GeneralPaperClosedStrategyDriver.close (fun w => w) A raw.1
  (⟨raw.1, stored.1⟩, raw.2 + stored.2 + 128 * A)

theorem data {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (parsed : Parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    (run model Wv Ws A parsed values v hv b hb).1 =
      (GeneralPaperClosedStrategyDriver.bit model Wv Ws A parsed.words values v hv b hb).1 := by
  have hk : (GeneralPaperBinaryAccuracy.prepare (fun w => w) A parsed.words).1 = parsed.exponent := by
    rw [GeneralPaperBinaryAccuracy.prepare_data, parsed.correct]
  dsimp only [run, GeneralPaperClosedStrategyDriver.bit, GeneralPaperAccuracyStrategyDriver.bit]
  rw [hk]

theorem work_partition {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (parsed : Parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    (GeneralPaperClosedStrategyDriver.bit model Wv Ws A parsed.words values v hv b hb).2 =
      (run model Wv Ws A parsed values v hv b hb).2 +
        (GeneralPaperBinaryAccuracy.prepare (fun w => w) A parsed.words).2 + 64 * A := by
  have hk : (GeneralPaperBinaryAccuracy.prepare (fun w => w) A parsed.words).1 = parsed.exponent := by
    rw [GeneralPaperBinaryAccuracy.prepare_data, parsed.correct]
  dsimp only [run, GeneralPaperClosedStrategyDriver.bit, GeneralPaperAccuracyStrategyDriver.bit]
  rw [hk]
  ring

theorem work_le {n : ℕ} (model : RationalCostModel) (Wv Ws A : ℕ) (parsed : Parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    (run model Wv Ws A parsed values v hv b hb).2 ≤
      (GeneralPaperClosedStrategyDriver.bit model Wv Ws A parsed.words values v hv b hb).2 := by
  rw [work_partition]
  omega

end Blotto.GeneralPaperClosedParsedPreparation
