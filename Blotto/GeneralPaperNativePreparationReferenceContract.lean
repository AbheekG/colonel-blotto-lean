import Blotto.GeneralPaperFullPreparationReference

/-! Instantiate the complete native caller reserve from fixed arithmetic
preparation data. Native source reference/index floors are derived, not supplied.
The actual bit preparation window and full returned owner fit the same word.
Sharp asymptotic growth of this complete reserve remains a separate theorem. -/
namespace Blotto.GeneralPaperNativePreparationReferenceContract
open GeneralPaperSourceWordGrowth GeneralPaperEncodedScalarStorage
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def data {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) : GeneralPaperOriginalSourceValuePreparation.Output n :=
  (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1

def input {n : ℕ} (model : RationalCostModel) (k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) : Input :=
  GeneralPaperOriginalSourceValuePreparation.input (data model k values v hv) k B b hb hB

noncomputable def reserve {n : ℕ} (model : RationalCostModel) (C d W E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) : ℕ :=
  let p := data model k values v hv
  GeneralPaperFullPreparationReference.reserve model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
    p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced (input model k B values v hv b hb hB)

noncomputable def width {n : ℕ} (model : RationalCostModel) (C d E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) : ℕ :=
  let p := data model k values v hv
  GeneralPaperFullPreparationReference.width model C d E k (GeneralPaperValueRoundingInputPrice.inputSize values)
    p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced (input model k B values v hv b hb hB)

theorem native_floors {n : ℕ} (model : RationalCostModel) (C d E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let W := width model C d E k B values v hv b hb hB
    binaryWordWidth (n+1)≤W ∧
    GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1 k B b hb hB)≤W ∧
    reserve model C d W E k B values v hv b hb hB<2^W := by
  dsimp only
  let p := data model k values v hv
  let x := input model k B values v hv b hb hB
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width p.reduced.m k
  refine ⟨GeneralPaperFullPreparationReference.original_index_floor model C d E k S p.Qv B H p.reduced x,?_,
    GeneralPaperFullPreparationReference.capacity model C d E k S p.Qv B H p.reduced x⟩
  rw [GeneralPaperOriginalSourceDataCalibration.input_reference_models]
  exact GeneralPaperFullPreparationReference.source_floor model C d E k S p.Qv B H p.reduced x

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    GeneralPaperReferenceScaling.Scale (fun W => reserve model C d W E k B values v hv b hb hB) := by
  unfold reserve
  dsimp only
  fun_prop

theorem bit_profile_models {n : ℕ} (model : RationalCostModel) (C d W E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    GeneralPaperFullPreparationReference.bitProfile model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
      p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced=
    GeneralPaperFullPreparationReference.bitProfile model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
      (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
      (data model k values v hv).reduced := by
  dsimp only
  rw [GeneralPaperOriginalSourceDataCalibration.reduced_models,GeneralPaperOriginalSourceDataCalibration.denominator_models]
  rfl

theorem frame_profile_models {n : ℕ} (model : RationalCostModel) (C d W E k B : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    GeneralPaperFullPreparationReference.frameProfile model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
      p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced=
    GeneralPaperFullPreparationReference.frameProfile model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
      (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
      (data model k values v hv).reduced := by
  dsimp only
  rw [GeneralPaperOriginalSourceDataCalibration.reduced_models,GeneralPaperOriginalSourceDataCalibration.denominator_models]
  rfl

theorem bit_contract {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (B : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize words
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) 1 words).1
    let W := width model C d E k B values v hv b hb hB
    let nativeK := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W nativeK values v hv).1
    ∀ (cS : SourceCursor p.reduced.m nativeK p.Qv) (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows nativeK p.reduced)),
      let observed := GeneralPaperClosedStrategyConstructionStorage.window W
        (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).1
        (GeneralPaperAccuracyStrategyDriver.bit model W W W words values v hv b hb).2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W words values v hv b hb cS cD)
      observed≤reserve model C d W E k B values v hv b hb hB ∧ observed<2^W ∧
        GeneralPaperClosedDescriptionStorage.preparedFoot W (GeneralPaperClosedStrategyDriver.bit model W W W words values v hv b hb).1<2^W := by
  dsimp only
  intro cS cD
  let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize words
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) 1 words).1
  let W := width model C d E k B values v hv b hb hB
  let nativeK := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W nativeK values v hv).1
  have hK : nativeK=k := GeneralPaperOriginalSourceDataCalibration.exponent_models W words
  have hf := native_floors model C d E k B values v hv b hb hB
  change binaryWordWidth (n+1)≤W ∧ _ ∧ reserve model C d W E k B values v hv b hb hB<2^W at hf
  have hReference : GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input p nativeK B b hb hB)≤W := by
    dsimp only [p]
    rw [hK]
    exact hf.2.1
  have h := GeneralPaperClosedStrategyConstructionStorage.native_bit_bounded hg W B words values v hv b hb hB hf.1 hReference cS cD
  have hWindow := h.1
  have hReturn := h.2.2
  change _≤GeneralPaperFullPreparationReference.bitProfile model C d W E nativeK
    (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m nativeK) p.reduced at hWindow
  change _≤GeneralPaperFullPreparationReference.bitProfile model C d W E nativeK
    (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m nativeK) p.reduced at hReturn
  have hProfile : GeneralPaperFullPreparationReference.bitProfile model C d W E nativeK
      (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m nativeK) p.reduced=
      GeneralPaperFullPreparationReference.bitProfile model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
        (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
        (data model k values v hv).reduced := by
    dsimp only [p]
    rw [hK]
    exact bit_profile_models model C d W E k B values v hv
  rw [hProfile] at hWindow hReturn
  have hReserve := GeneralPaperFullPreparationReference.bit_le model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
    (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
    (data model k values v hv).reduced (input model k B values v hv b hb hB)
  change _≤reserve model C d W E k B values v hv b hb hB at hReserve
  exact ⟨hWindow.trans hReserve,(hWindow.trans hReserve).trans_lt hf.2.2,(hReturn.trans hReserve).trans_lt hf.2.2⟩

theorem frame_contract {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (E B : ℕ) (frame : List Bool) (hc : frame.length≤E) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let k := parsed.1.exponent
    let W := width model C d E k B values v hv b hb hB
    ∀ (_hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some parsed),
      let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
      ∀ (cS : SourceCursor p.reduced.m k p.Qv) (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor p.reduced (rows k p.reduced)),
        let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W k values v hv b hb).1,parsed.2)
        let observed := GeneralPaperClosedStrategyConstructionStorage.frameWindow model W frame values v hv b hb raw
          (GeneralPaperFramedStrategyConstructionStorage.window model W frame parsed values v hv b hb cS cD)
        observed≤reserve model C d W E k B values v hv b hb hB ∧ observed<2^W ∧
          GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W frame values v hv b hb<2^W := by
  dsimp only
  intro hRead cS cD
  let k := parsed.1.exponent
  let W := width model C d E k B values v hv b hb hB
  let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
  have hf := native_floors model C d E k B values v hv b hb hB
  change binaryWordWidth (n+1)≤W ∧ _ ∧ reserve model C d W E k B values v hv b hb hB<2^W at hf
  have h := GeneralPaperClosedStrategyConstructionStorage.native_frame_bounded hg W E B frame hc parsed hRead
    values v hv b hb hB hf.1 hf.2.1 cS cD
  have hWindow := h.1
  have hReturn := h.2.2
  change _≤GeneralPaperFullPreparationReference.frameProfile model C d W E k
    (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced at hWindow
  change _≤GeneralPaperFullPreparationReference.frameProfile model C d W E k
    (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced at hReturn
  have hProfile := frame_profile_models model C d W E k B values v hv
  rw [hProfile] at hWindow hReturn
  have hReserve := GeneralPaperFullPreparationReference.frame_le model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
    (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
    (data model k values v hv).reduced (input model k B values v hv b hb hB)
  change _≤reserve model C d W E k B values v hv b hb hB at hReserve
  exact ⟨hWindow.trans hReserve,(hWindow.trans hReserve).trans_lt hf.2.2,(hReturn.trans hReserve).trans_lt hf.2.2⟩

theorem rejected_contract {n : ℕ} (model : RationalCostModel) (C d E k B : ℕ) (frame : List Bool) (hc : frame.length≤E)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let W := width model C d E k B values v hv b hb hB
    ∀ (_hRead : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=none),
      let observed := GeneralPaperClosedStrategyConstructionStorage.rejectedWindow model W frame values v hv b hb
        (GeneralPaperFramedStrategyConstructionStorage.rejectedWindow model W frame values v hv b hb)
      observed≤reserve model C d W E k B values v hv b hb hB ∧ observed<2^W ∧
        GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W frame values v hv b hb=0 := by
  dsimp only
  intro hRead
  let W := width model C d E k B values v hv b hb hB
  have hf := native_floors model C d E k B values v hv b hb hB
  have h := GeneralPaperClosedStrategyConstructionStorage.native_rejected_bounded model W E B frame hc values v hv b hb hB hRead
  have hReserve := GeneralPaperFullPreparationReference.rejected_le model C d W E k (GeneralPaperValueRoundingInputPrice.inputSize values)
    (data model k values v hv).Qv B (GeneralPaperSourcePairAnchorHeights.width (data model k values v hv).reduced.m k)
    (data model k values v hv).reduced (input model k B values v hv b hb hB)
  change _≤reserve model C d W E k B values v hv b hb hB at hReserve
  exact ⟨h.1.trans hReserve,(h.1.trans hReserve).trans_lt hf.2.2,h.2.2⟩

theorem canonical_reader {n : ℕ} (model : RationalCostModel) (C d B : ℕ) (epsilon : ℚ) (hE : 0<epsilon)
    (suffix : List Bool) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let E := 2*rationalWordWidth epsilon+suffix.length
    let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    let W := width model C d E k B values v hv b hb hB
    ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W
      (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix)).1=some (parsed,suffix) ∧
      parsed.exponent=k ∧ GeneralPaperBinaryAccuracyConstructionStorage.inputSize parsed.words+1=rationalWordWidth epsilon ∧
      reserve model C d W E k B values v hv b hb hB<2^W := by
  dsimp only
  obtain ⟨parsed,hr,hk,hSize,_,_⟩ := GeneralPaperFramedAccuracyConstructionStorage.canonical_frame_contract
    (width model C d (2*rationalWordWidth epsilon+suffix.length) (GeneralPaperDyadicAccuracy.prepare epsilon).exponent B values v hv b hb hB)
    epsilon hE suffix
  exact ⟨parsed,hr,hk,hSize,(native_floors model C d (2*rationalWordWidth epsilon+suffix.length)
    (GeneralPaperDyadicAccuracy.prepare epsilon).exponent B values v hv b hb hB).2.2⟩

theorem canonical_frame_capacity {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (B : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (suffix : List Bool) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix
    let E := 2*rationalWordWidth epsilon+suffix.length
    let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    let W := width model C d E k B values v hv b hb hB
    ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some (parsed,suffix) ∧ parsed.exponent=k ∧
      ∀ (cS : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent values v hv).1.reduced.m
          parsed.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent values v hv).1.Qv)
        (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor
          (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent values v hv).1.reduced
          (rows parsed.exponent (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent values v hv).1.reduced)),
        GeneralPaperClosedStrategyConstructionStorage.frameWindow model W frame values v hv b hb
          ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.exponent values v hv b hb).1,suffix)
          (GeneralPaperFramedStrategyConstructionStorage.window model W frame (parsed,suffix) values v hv b hb cS cD)<2^W ∧
        GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W frame values v hv b hb<2^W := by
  dsimp only
  let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix
  let E := 2*rationalWordWidth epsilon+suffix.length
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  let W := width model C d E k B values v hv b hb hB
  obtain ⟨parsed,hr,hk,_,_⟩ := canonical_reader model C d B epsilon hE suffix values v hv b hb hB
  have hLength : frame.length≤E := by
    dsimp only [frame,E]
    rw [List.length_append,GeneralPaperBinaryAccuracy.input_length]
  have hWord : width model C d E parsed.exponent B values v hv b hb hB=W := by
    rw [hk]
  have hFrame := frame_contract hg E B frame hLength (parsed,suffix) values v hv b hb hB
  dsimp only at hFrame
  rw [hWord] at hFrame
  refine ⟨parsed,hr,hk,?_⟩
  intro cS cD
  have h := hFrame hr cS cD
  exact ⟨h.2.1,h.2.2⟩

end Blotto.GeneralPaperNativePreparationReferenceContract
