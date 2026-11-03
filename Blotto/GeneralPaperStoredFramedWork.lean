import Blotto.GeneralPaperStoredCanonicalFrame

/-! Exact pass composition makes the parser-to-stored continuation's work
reviewable. The old word-input preparation price minus its single accuracy
preparation equals this continuation's source price; no second accuracy
pass is executed or charged. Sharp full installation rates remain open. -/
namespace Blotto.GeneralPaperStoredFramedWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperBinaryAccuracy (Parsed)
open GeneralPaperStoredParsedPreparation (width prepare input)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

theorem prepared_price_identity {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (prepare model A K values v hv budget parsed).2 + (GeneralPaperBinaryAccuracy.prepare id A parsed.words).2 =
      (GeneralPaperEqualCopiedPipeline.run model A K (input model values v hv budget parsed)).2 := by
  rw [GeneralPaperStoredParsedPreparation.prepared_work,GeneralPaperEqualCopiedPipeline.work]
  have hk := GeneralPaperEqualInputInitialization.initialized_exponent model A K (input model values v hv budget parsed)
  change (GeneralPaperBinaryAccuracy.prepare id A parsed.words).1 = parsed.exponent at hk
  simp only [GeneralPaperEqualInputInitialization.prepareReference,input,hk]
  ring

theorem construction_work {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (parsed : Parsed) :
    (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).2 =
      (prepare model A K values v hv budget parsed).2 +
      (GeneralPaperStoredSelectedConstruction.run model (GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed))
        (prepare model A K values v hv budget parsed).1).2 +
      64 * (GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed) + width model A K values v hv budget parsed + 1) := by
  let prepared := prepare model A K values v hv budget parsed
  let W := GeneralPaperEqualInputDomain.word K (input model values v hv budget parsed)
  obtain ⟨inner,hBuilt,hWork,_⟩ := GeneralPaperStoredSelectedConstruction.source model W W parsed.exponent values v hv budget prepared.1
  simp only [GeneralPaperStoredParsedPreparation.run,hBuilt,GeneralPaperSamplerRecordInstallation.attach,prepared,W] at *
  exact congrArg (fun w => (prepare model A K values v hv budget parsed).2 + w + 64 * (W + width model A K values v hv budget parsed + 1)) hWork

theorem frame_work {n : ℕ} (model : RationalCostModel) (A K : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) (frame suffix : List Bool) (parsed : Parsed)
    (hRead : (GeneralPaperBinaryAccuracy.read id A frame).1 = some (parsed,suffix)) :
    (GeneralPaperStoredFramedPreparation.run model A K values v hv budget frame).2 =
      (GeneralPaperBinaryAccuracy.read id A frame).2 +
      (GeneralPaperStoredParsedPreparation.run model A K values v hv budget parsed).2 +
      64 * (A + width model A K values v hv budget parsed + 1) := by
  obtain ⟨inner,hBuild,hWork,_⟩ := GeneralPaperStoredParsedPreparation.source model A K values v hv budget parsed
  have h := (GeneralPaperStoredFramedPreparation.on_parsed model A K values v hv budget frame suffix parsed hRead inner hBuild).2
  rw [h]
  change _ + inner.work + _ = _
  rw [hWork]

theorem parser_bound (A : ℕ) (frame : List Bool)
    (hCap : 1 + binaryWordWidth (frame.length + 1) ≤ A) :
    (GeneralPaperBinaryAccuracy.read id A frame).2 ≤ 256 * (frame.length + 1) * A :=
  GeneralPaperBinaryAccuracy.read_work id (fun _ _ h => h) A frame hCap

theorem canonical_parser_bound (A : ℕ) (eps : ℚ) (hPositive : 0 < eps)
    (hCap : 1 + binaryWordWidth (2 * rationalWordWidth eps + 1) ≤ A) :
    (GeneralPaperBinaryAccuracy.read id A (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive))).2 ≤
      256 * (2 * rationalWordWidth eps + 1) * A := by
  have h := parser_bound A (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input eps hPositive))
    (by simpa only [GeneralPaperBinaryAccuracy.input_length] using hCap)
  simpa only [GeneralPaperBinaryAccuracy.input_length] using h

end Blotto.GeneralPaperStoredFramedWork
