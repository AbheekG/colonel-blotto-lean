import Blotto.GeneralPaperMixedInitializerCalibration

/-! Complete construction storage after accuracy has already been selected.
The skipped accuracy pass is used only as an upper-bound observer. It is
absent from the executed parsed continuation. -/
namespace Blotto.GeneralPaperClosedParsedStorage
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

theorem closed_window_mono {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n)
    (work work' space space' : ℕ) (hWork : work ≤ work') (hSpace : space ≤ space') :
    GeneralPaperClosedStrategyConstructionStorage.window W raw work space ≤
      GeneralPaperClosedStrategyConstructionStorage.window W raw work' space' := by
  have hf := GeneralPaperMixedPrimitiveStorage.fields_mono W
    (GeneralPaperClosedStrategyConstructionStorage.controls W raw work)
    (GeneralPaperClosedStrategyConstructionStorage.controls W raw work') (by
      dsimp only [GeneralPaperClosedStrategyConstructionStorage.controls]
      simp [List.forall₂_cons, hWork])
  unfold GeneralPaperClosedStrategyConstructionStorage.window
  omega

abbrev SourceCursor {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :=
  GeneralPaperOriginalSourceDriverConstructionStorage.SourceCursor
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv

abbrev DescriptionCursor {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :=
  GeneralPaperStrategyDescriptionConstructionStorage.Cursor
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced
    (rows k (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced)

noncomputable def window {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1)
    (cS : SourceCursor model W k values v hv) (cD : DescriptionCursor model W k values v hv) : ℕ :=
  let raw := GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb
  GeneralPaperClosedStrategyConstructionStorage.window W raw.1 raw.2
    (GeneralPaperAccuracyStrategyConstructionStorage.exponentWindow model W k values v hv b hb cS cD)

theorem le_redundant_accuracy {n : ℕ} (model : RationalCostModel) (W : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
    ∀ (cS : SourceCursor model W k values v hv) (cD : DescriptionCursor model W k values v hv),
      window model W k values v hv b hb cS cD ≤
        GeneralPaperClosedStrategyConstructionStorage.window W
          (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1
          (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2
          (GeneralPaperAccuracyStrategyConstructionStorage.window model W words values v hv b hb cS cD) := by
  dsimp only
  intro cS cD
  apply closed_window_mono
  · change (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W _ values v hv b hb).2 ≤
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2 +
        (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W _ values v hv b hb).2 + 64 * W
    omega
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.window
    omega

theorem returned_covered {n : ℕ} (model : RationalCostModel) (W : ℕ) (parsed : GeneralPaperBinaryAccuracy.Parsed)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1)
    (cS : SourceCursor model W parsed.exponent values v hv)
    (cD : DescriptionCursor model W parsed.exponent values v hv) :
    GeneralPaperClosedDescriptionStorage.preparedFoot W
      (GeneralPaperClosedParsedPreparation.run model W W W parsed values v hv b hb).1 ≤
      window model W parsed.exponent values v hv b hb cS cD :=
  GeneralPaperClosedStrategyConstructionStorage.returned_covered W
    (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.exponent values v hv b hb).1 _ _

end Blotto.GeneralPaperClosedParsedStorage
