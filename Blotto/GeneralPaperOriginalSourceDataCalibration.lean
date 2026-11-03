import Blotto.GeneralPaperClosedStrategyConstructionStorage

/-! Cost/reference calibration never changes the native reduction data or
second denominator. The complete source reference depends only on its four
size parameters; all weights and erased proof witnesses remain native. -/
namespace Blotto.GeneralPaperOriginalSourceDataCalibration
open GeneralPaperSourceWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem reduced_models {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced=
      (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1.reduced :=
  GeneralPaperOriginalValueReduction.models_data model W k values v hv

theorem denominator_models {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv=
      (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1.Qv := by
  rw [GeneralPaperOriginalSourceValuePreparation.denominator_data,GeneralPaperOriginalSourceValuePreparation.denominator_data,
    GeneralPaperOriginalValueReduction.models_data model W k values v hv]
  exact congrArg Prod.snd (GeneralPaperValueRoundingPaperContract.models_data model W 512 k _
    (GeneralPaperOriginalValueReduction.selector false model 1 k values v hv) (fun _ => rfl))

theorem reference_congr (C d : ℕ) (x y : Input) (hm : x.m=y.m) (hk : x.k=y.k) (hQ : x.Qv=y.Qv) (hB : x.B=y.B) :
    GeneralPaperFastDriverReference.width C d x=GeneralPaperFastDriverReference.width C d y := by
  unfold GeneralPaperFastDriverReference.width GeneralPaperFastDriverReference.profile GeneralPaperFastDriverReference.padding
    GeneralPaperFastDriverIndexReference.size GeneralPaperFastDriverIndexReference.core GeneralPaperFastDriverIndexReference.gridCount alphabet
  rw [hm,hk,hQ,hB]

theorem input_reference_models {n : ℕ} (model : RationalCostModel) (C d W k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1 k B b hb hB)=
    GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input
      (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1 k B b hb hB) := by
  apply reference_congr
  · exact congrArg GeneralPaperReducedValuesDriver.Output.m (reduced_models model W k values v hv)
  · rfl
  · exact denominator_models model W k values v hv
  · rfl

theorem exponent_models (W : ℕ) (words : BinaryAccuracyWords) :
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1=
      (GeneralPaperBinaryAccuracy.prepare (fun w => w) 1 words).1 := by
  rw [GeneralPaperBinaryAccuracy.prepare_data,GeneralPaperBinaryAccuracy.prepare_data]

theorem parsed_exponent (parsed : GeneralPaperBinaryAccuracy.Parsed) :
    parsed.exponent=(GeneralPaperBinaryAccuracy.prepare (fun w => w) 1 parsed.words).1 := by
  rw [parsed.correct,GeneralPaperBinaryAccuracy.prepare_data]

end Blotto.GeneralPaperOriginalSourceDataCalibration
