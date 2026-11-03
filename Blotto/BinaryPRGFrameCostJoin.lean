import Blotto.BinaryPRGSeedPreparedRun

/-! The incoming raw request supplies every argument of the complete recorded
input/seed/sampler/output envelope. Rejected runs have no returned output ledger.
This joins recorded Boolean/arithmetic/cell components; it does not certify a
physical execution, compiler, controller, address model or live working space.
The original runner, exact bytes, laws, hard budgets and continuous scopes are
unchanged. -/

namespace Blotto.BinaryPRGFrameCostJoin
set_option exponentiation.threshold 1024
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGAccuracyRulerRequest BinaryPRGPreparation
open scoped BigOperators

theorem read_stored_width (frame : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) :
    BinaryPRGPreparationWork.storedInputWidth parsed.1.2.request.prepared.original ≤ frame.length + 2 := by
  unfold BinaryPRGAccuracyRulerRequest.read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i game hg
    have hOld : (BinaryPRGNormalizedFrameWork.read frame).1 = some game :=
      (BinaryPRGNormalizedFrameWork.read_state frame).trans
        ((BinaryPRGStoredDimensionFrame.read_state frame).symm.trans hg)
    have hw := BinaryDecodedInputLength.parsed_storedInputWidth frame game hOld
    split at h
    · cases h
    · rename_i checked hc
      have hp := BinaryPRGPreparation.prepareChecked_data game.1.2.game.input game.1.2.game.canonical checked
        ((BinaryPRGMeasuredPreparation.prepareChecked_state _ _).symm.trans hc)
      obtain ⟨accuracy,ha,hOut⟩ := Option.map_eq_some_iff.mp h
      subst parsed
      change BinaryPRGPreparationWork.storedInputWidth checked.val.original ≤ _
      rw [hp]
      exact hw

theorem source_width_from_stored {n : ℕ} (request : BinaryPRGRequest.Request n) :
    request.source.originalInputWordWidth ≤ n + 2 + 2 * BinaryPRGPreparationWork.storedInputWidth request.prepared.original := by
  have ha := rationalWordWidth_of_height (BinaryStoredWordSumWork.stored_value_height
    request.prepared.original.a request.valid.2.1.1.1)
  have hb := rationalWordWidth_of_height (BinaryStoredWordSumWork.stored_value_height
    request.prepared.original.b request.valid.2.1.2.1.1)
  have hv : (∑ j, rationalWordWidth (value (request.prepared.original.values.read j))) ≤
      n + 2 * (∑ j, width (request.prepared.original.values.read j)) := by
    calc
      _ ≤ ∑ j, (1 + 2 * width (request.prepared.original.values.read j)) :=
        Finset.sum_le_sum (fun j _ => rationalWordWidth_of_height
          (BinaryStoredWordSumWork.stored_value_height _ (request.valid.2.1.2.2 j).1))
      _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]
  change rationalWordWidth (value request.prepared.original.a) +
    rationalWordWidth (value request.prepared.original.b) +
      (∑ j, rationalWordWidth (value (request.prepared.original.values.read j))) ≤ _
  unfold BinaryPRGPreparationWork.storedInputWidth
  omega

theorem read_source_width (frame : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) :
    parsed.1.2.request.source.originalInputWordWidth ≤ 3 * frame.length + 6 := by
  have hs := source_width_from_stored parsed.1.2.request
  have hw := read_stored_width frame parsed h
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h
  omega

theorem expressionHeightBudget_affine (s d : ℕ) :
    expressionHeightBudget s d = s * 2 ^ d + (2 ^ d - 1) := by
  have hp : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by decide)
  unfold expressionHeightBudget
  rw [Nat.add_mul,Nat.one_mul]
  omega

macro "unfold_terminal_envelope" : tactic => `(tactic|
  simp only [BinaryCachedTerminalEmissionRun.bound,
    BinaryCachedTerminalEmissionRun.emissionBound, BinaryCachedTerminalEmissionRun.groupHeight,
    BinaryCachedTerminalPrimitiveRun.bound,
    BinaryGroupRetainedPrimitiveRun.descriptorDrawBound, BinaryGroupRetainedPrimitiveRun.mixedBound,
    BinaryGroupRetainedPrimitiveRun.factoryBound,
    BinaryFourSpecRetainedWork.runBound, BinaryFourOrderedRetainedWork.runBound,
    BinarySmallRetainedPrimitiveWork.runBound, BinarySmallRetainedPrimitiveWork.rootBound,
    BinarySmallRootPrimitiveRun.rootBound, BinarySmallUniformFactoryDraw.bound,
    BinarySmallUniformDrawWork.bound, BinaryReflectedFactoryRun.bound,
    BinaryReflectedMeasuredRun.bound, BinaryReflectedResourceWork.bound,
    BinaryReflectedPreparedDraw.bound, BinaryReflectedCategoricalWork.bound,
    BinaryGluingDrawWork.partialBound, BinaryStoredSegmentChoiceWork.selectionBound,
    BinaryStoredSegmentDrawWork.pointBound, BinaryStoredCoinIndexedWork.bound,
    BinaryUnorderedThreeFactoryWork.bound, BinaryOrderedThreeFactoryWork.bound,
    BinaryThreeFactoryWork.bound, BinaryFourNativeOrderWork.guardBound,
    BinaryReflectedSetupCache.bound, BinaryReflectedSetupWork.bound,
    BinaryCachedFourParameterWork.parameterBound, BinaryFourParentCompiler.workBound,
    BinaryFourParentCompiler.parentWorkBound, BinaryThreeInputCompiler.workBound,
    BinaryOverlapInputPreparation.evaluationWorkBound,
    BinarySmallUniformFactoryWork.bound, BinarySmallUniformFactoryWork.prepareBound,
    BinarySmallUniformFactoryWork.descriptorBound,
    BinaryNestedTerminalPreparationWork.bound, BinaryReflectedSelectedEmissionWork.bound,
    BinaryReflectedFactoryPrepared.bound, BinaryNestedSpecFactoryWork.bound,
    BinaryNestedOrderedFactoryWork.bound, BinaryNestedOrderedFactoryWork.secondBound,
    BinaryNestedOrderedFactoryWork.thirdBound, BinaryNestedOrderedFactoryWork.familyBound,
    BinaryNestedOrderedFactoryWork.mixtureBound, BinaryNestedOrderedFactoryWork.height,
    BinaryNestedOrderedFactoryWork.width, BinaryNestedFamilyFactoryWork.bound,
    BinaryNestedFirstFactoryWork.firstBound, BinaryNestedFirstFactoryWork.descriptorBound,
    BinaryNestedRemainingFactoryWork.secondBound, BinaryNestedRemainingFactoryWork.residualBound,
    BinaryThreeResourceRunWork.pairTotalBound, BinaryThreeResourceRunWork.padBound,
    BinaryThreeResourceRunWork.bodyBound, BinaryThreeResourceExecution.pairBound,
    BinaryThreeResourceExecution.selectBound, BinaryThreeResourceHeight.coinWidth,
    BinaryThreeResourceHeight.resourceHeight, BinaryFactoryHeight.opcodeBound,
    BinaryFactoryHeight.compareBound, BinaryRationalExpression.uniformPrice,
    expressionHeightBudget_affine])

theorem terminal_bound_mono {n m s t K Q N M : ℕ}
    (hn : n ≤ m) (hs : s ≤ t) (hK : K ≤ Q) (hN : N ≤ M) :
    BinaryCachedTerminalEmissionRun.bound n s K N ≤ BinaryCachedTerminalEmissionRun.bound m t Q M := by
  unfold_terminal_envelope
  gcongr

def outputEnvelope (t : ℕ) : ℕ :=
  (7554000 * t + 96000) * (8 * t) ^ 3 + 52 * (3015 * t) * (8 * t) +
    BinaryCachedTerminalEmissionRun.bound t (32 * t) (5 * t) (3015 * t) +
      BinaryPRGOutputRun.fallbackBound t (32 * t) +
        t * BinaryFactoryHeight.opcodeBound (expressionHeightBudget (16 * t) 75) +
          (4 * (2 * (t + 1) + 1 + t * (4 * (1 + 2 * expressionHeightBudget (16 * t) 76) + 3)) + 2 * t)

set_option exponentiation.threshold 1024 in
set_option maxHeartbeats 2000000 in
theorem outputEnvelope_polynomial (t : ℕ) (ht : 1 ≤ t) : outputEnvelope t ≤ 2 ^ 384 * t ^ 4 := by
  have h0 : 1 ≤ t ^ 4 := Nat.one_le_pow 4 t ht
  have h1 : t ≤ t ^ 4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 1 ≤ 4)
  have h2 : t ^ 2 ≤ t ^ 4 := Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 2 ≤ 4)
  have h3 : t ^ 3 ≤ t ^ 4 := Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 3 ≤ 4)
  unfold outputEnvelope BinaryPRGOutputRun.fallbackBound BinaryFactoryHeight.opcodeBound
  unfold_terminal_envelope
  norm_num only [Nat.reducePow,Nat.reduceSub,Nat.reduceMul,Nat.reduceAdd]
  simp (disch := omega) only [max_eq_left]
  ring_nf
  nlinarith only [h0,h1,h2,h3]

theorem request_bound_from_caps {n : ℕ} (request : BinaryPRGRequest.Request n) (length : ℕ)
    (hn : n ≤ length) (hK : request.precision ≤ length + 5)
    (hW : request.source.originalInputWordWidth ≤ 3 * length + 6) :
    BinaryPRGOutputRun.bound request ≤ outputEnvelope (length + 1) := by
  let t := length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hnT : n ≤ t := by dsimp [t]; omega
  have hWT : request.source.originalInputWordWidth + 2 ≤ 8 * t := by dsimp [t]; omega
  have hKT : request.precision ≤ 5 * t := by dsimp [t]; omega
  have hN : RationalLottoResourceSystem.coinBitBudget n request.precision ≤ 3015 * t := by
    unfold RationalLottoResourceSystem.coinBitBudget
    dsimp [t]
    omega
  have hInput : BinaryCachedGroupInputHeight.inputHeight request ≤ 32 * t := by
    unfold BinaryCachedGroupInputHeight.inputHeight
    omega
  have hRequest : BinaryCachedTerminalPrimitiveRun.requestHeight request ≤ 32 * t := by
    unfold BinaryCachedTerminalPrimitiveRun.requestHeight
    exact max_le hInput (by omega)
  have hBase : max (3 + request.source.originalInputWordWidth) (request.precision + 2) ≤ 16 * t := by
    apply max_le <;> dsimp [t] <;> omega
  have hHeight : BinaryPRGOutputPrimitiveWork.normalizedHeight request request.precision ≤ expressionHeightBudget (16 * t) 75 := by
    unfold BinaryPRGOutputPrimitiveWork.normalizedHeight
    simp only [expressionHeightBudget_affine]
    gcongr
  have hOutputHeight : BinaryPRGOutputPrimitiveWork.outputHeight request request.precision ≤ expressionHeightBudget (16 * t) 76 := by
    unfold BinaryPRGOutputPrimitiveWork.outputHeight
    simp only [expressionHeightBudget_affine]
    gcongr
  have hHeader : binaryWordWidth n ≤ t + 1 := by
    unfold binaryWordWidth
    exact Nat.add_le_add_right ((Nat.log2_le_self n).trans hnT) 1
  have hSampling : BinaryPRGOutputRun.samplingBound request request.precision ≤
      (7554000 * t + 96000) * (8 * t) ^ 3 + 52 * (3015 * t) * (8 * t) +
        BinaryCachedTerminalEmissionRun.bound t (32 * t) (5 * t) (3015 * t) := by
    unfold BinaryPRGOutputRun.samplingBound
    apply Nat.add_le_add
    · gcongr
    · exact terminal_bound_mono hnT hRequest hKT hN
  have hFallback : BinaryPRGOutputRun.fallbackBound n (BinaryCachedGroupInputHeight.inputHeight request) ≤
      BinaryPRGOutputRun.fallbackBound t (32 * t) := by
    unfold BinaryPRGOutputRun.fallbackBound
    gcongr
  have hScaling : n * BinaryFactoryHeight.opcodeBound (BinaryPRGOutputPrimitiveWork.normalizedHeight request request.precision) ≤
      t * BinaryFactoryHeight.opcodeBound (expressionHeightBudget (16 * t) 75) := by
    unfold BinaryFactoryHeight.opcodeBound
    exact Nat.mul_le_mul hnT (Nat.mul_le_mul_left 12000
      (Nat.pow_le_pow_left (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hHeight) 2) 3))
  have hFrame : 4 * (2 * binaryWordWidth n + 1 + n * (4 * BinaryPRGOutputPrimitiveWork.outputWidth request + 3)) + 2 * n ≤
      4 * (2 * (t + 1) + 1 + t * (4 * (1 + 2 * expressionHeightBudget (16 * t) 76) + 3)) + 2 * t := by
    unfold BinaryPRGOutputPrimitiveWork.outputWidth
    gcongr
  unfold BinaryPRGOutputRun.bound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hSampling hFallback) hScaling) hFrame

theorem read_output_bound (frame : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) :
    BinaryPRGOutputRun.bound parsed.1.2.request ≤ 2 ^ 384 * (frame.length + 1) ^ 4 :=
  (request_bound_from_caps parsed.1.2.request frame.length
    (BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h)
    (read_precision_bound frame parsed h) (read_source_width frame parsed h)).trans
      (outputEnvelope_polynomial (frame.length + 1) (by omega))

theorem run_returned_output_bound (rich : Bool) (frame seed : List Bool)
    (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (BinaryPRGSeedPreparedRun.run rich frame seed).1 = some returned) :
    returned.2.recorded ≤ 2 ^ 384 * (frame.length + 1) ^ 4 := by
  obtain ⟨parsed,hParsed,hBound⟩ := BinaryPRGSeedPreparedRun.run_output_recorded_bound rich frame seed returned h
  obtain ⟨native,hNative,hForget⟩ := Option.map_eq_some_iff.mp ((read_state frame).trans hParsed)
  have hSame := congrArg (fun selected : (Σ n, BinaryPRGRequest.Request n) × List Bool =>
    BinaryPRGOutputRun.bound selected.1.2) hForget
  change BinaryPRGOutputRun.bound native.1.2.request = BinaryPRGOutputRun.bound parsed.2 at hSame
  rw [← hSame] at hBound
  exact hBound.trans (read_output_bound frame native hNative)

/-- Only an actual returned sampler/output ledger is added to setup work. -/
def returnedRecorded (result : Option (List Bool × BinaryPRGOutputRun.Ledger)) : ℕ :=
  match result with
  | none => 0
  | some returned => returned.2.recorded

def recorded (rich : Bool) (frame seed : List Bool) : ℕ :=
  (BinaryPRGSeedPreparedRun.run rich frame seed).2.recorded +
    returnedRecorded (BinaryPRGSeedPreparedRun.run rich frame seed).1

/-- An explicit polynomial in the physical incoming request length alone. -/
def polynomialBound (length : ℕ) : ℕ := (8623936008 + 2 ^ 384) * (length + 1) ^ 4

theorem run_polynomial (rich : Bool) (frame seed : List Bool) :
    recorded rich frame seed ≤ polynomialBound frame.length := by
  have hSetup := BinaryPRGSeedPreparedRun.run_polynomial rich frame seed
  have hOutput : returnedRecorded (BinaryPRGSeedPreparedRun.run rich frame seed).1 ≤
      2 ^ 384 * (frame.length + 1) ^ 4 := by
    cases h : (BinaryPRGSeedPreparedRun.run rich frame seed).1 with
    | none => exact Nat.zero_le _
    | some returned => exact run_returned_output_bound rich frame seed returned h
  unfold recorded polynomialBound
  exact (Nat.add_le_add hSetup hOutput).trans_eq (by unfold BinaryPRGSeedPreparedRun.polynomialBound; ring)

theorem run_returned_polynomial (rich : Bool) (frame seed : List Bool)
    (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (BinaryPRGSeedPreparedRun.run rich frame seed).1 = some returned) :
    (BinaryPRGSeedPreparedRun.run rich frame seed).2.recorded + returned.2.recorded ≤ polynomialBound frame.length := by
  simpa only [recorded,h,returnedRecorded] using run_polynomial rich frame seed

/-- Cost composition preserves the exact original framed result and ledger. -/
theorem run_exact_and_polynomial (rich : Bool) (frame seed : List Bool) :
    (BinaryPRGSeedPreparedRun.run rich frame seed).1 = BinaryPRGOutputRun.run rich frame seed ∧
      recorded rich frame seed ≤ polynomialBound frame.length :=
  ⟨BinaryPRGSeedPreparedRun.run_state rich frame seed,run_polynomial rich frame seed⟩

end Blotto.BinaryPRGFrameCostJoin
