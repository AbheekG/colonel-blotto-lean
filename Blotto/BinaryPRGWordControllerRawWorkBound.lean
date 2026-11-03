import Blotto.BinaryPRGWordControllerRawWork

/-! Incoming physical frame length derives all parameters of the joined
executed-controller source ledger.  The quartic bound includes real reached
Store preparation and every raw rejection, and uses each actual arithmetic
backend.  It is the Boolean/list/copy/controller source work model stated by
RawWork; no physical-address/compiler or sharp fast-bit contract is inferred. -/

namespace Blotto.BinaryPRGWordControllerRawWorkBound
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGWordControllerRawWork
open BinaryPRGOutputPrimitiveWork RationalLottoResourceSystem
set_option exponentiation.threshold 1024

def booleanResourceEnvelope (n W indexWidth N : ℕ) : ℕ :=
  BinaryPRGWordControllerBooleanResourceSourceWork.inputBound n (3 + 2 * W) +
    BinaryPRGWordControllerBooleanResourceInitial.initialBound (n + 1) (3 + 2 * W) n + 2 * indexWidth + 1 +
    (n + 1) * (BinaryPRGWordControllerBooleanResourcePair.bound (n + 1) (3 + 2 * W) + 1 +
      BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound (n + 1) (3 + 2 * W) n + 12 * (2 + 2 * W) +
        BinaryWordIndexCoinController.allowance (1 + 2 * W) indexWidth + 2) +
    N * BinaryWordIndexCoinController.allowance (1 + 2 * W) indexWidth +
    BinaryPRGWordControllerBooleanResourceSourceWork.outputBound n (n + 1) (3 + 2 * W) + 2

macro "unfold_boolean_resource_envelope" : tactic => `(tactic|
  simp only [booleanResourceEnvelope,BinaryPRGWordControllerBooleanResourceSourceWork.initialBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.inputBound,
    BinaryPRGWordControllerBooleanResourceInitial.initialBound,BinaryPRGWordControllerBooleanResourceInitial.addressBound,
    BinaryPRGWordControllerBooleanResourceLoopWork.widthBound,BinaryPRGWordControllerBooleanResourceLoopWork.bound,
    BinaryPRGWordControllerBooleanResourceLoopWork.pairBound,BinaryPRGWordControllerBooleanResourcePair.bound,
    BinaryPRGWordControllerPairOutputWork.traceBound,BinaryPRGWordControllerPairRegisters.instructionBound,
    BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound,BinaryPRGWordControllerBooleanResourceUpdateWork.fractionalBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.outputBound,BinaryPRGWordControllerBooleanResourceSourceWork.rowsBound,
    BinaryWordIndexCoinController.allowance])

macro "unfold_boolean_three_envelope" : tactic => `(tactic|
  simp only [BinaryPRGWordControllerBooleanResourceThreeWork.sourceBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.sourceEnvelope,BinaryPRGWordControllerBooleanResourceThreeWork.widthBound,
    BinaryPRGWordControllerBooleanResourceThreeWork.bound,BinaryPRGWordControllerBooleanResourceThreeWork.pairBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.inputBound,
    BinaryPRGWordControllerBooleanResourceInitial.initialBound,BinaryPRGWordControllerBooleanResourceInitial.addressBound,
    BinaryPRGWordControllerBooleanResourcePair.bound,BinaryPRGWordControllerPairOutputWork.traceBound,
    BinaryPRGWordControllerPairRegisters.instructionBound,BinaryPRGWordControllerBooleanResourceUpdateWork.updateBound,
    BinaryPRGWordControllerBooleanResourceUpdateWork.fractionalBound,
    BinaryPRGWordControllerBooleanResourceSourceWork.outputBound,BinaryPRGWordControllerBooleanResourceSourceWork.rowsBound,
    BinaryThreeResourceHeight.resourceHeight,BinaryThreeResourceHeight.coinWidth,
    BinaryPRGWordControllerThreeResource.bodyBound,BinaryWordIndexCoinController.allowance])

def resourceEnvelope (n W indexWidth N : ℕ) : ℕ :=
  n * (1000 * (2 + 2 * W)^2) + 8 * n + 2 + 2 * indexWidth + 1 +
    (n + 1) *
      (7 * (12000 * (4 + 2 * W)^3 + 28 * (7 + 4 * W) + 4) + 8 * (3 + 4 * W) + 12 +
        (24000 * (4 + 2 * W)^3 + 2000 * (2 + 2 * W)^2 + 25 + 4 * (n + 1) * (3 + 4 * W)) +
          12 * (2 + 2 * W) + BinaryWordIndexCoinController.allowance (1 + 2 * W) indexWidth + 2) +
            N * BinaryWordIndexCoinController.allowance (1 + 2 * W) indexWidth +
              booleanResourceEnvelope n W indexWidth N

theorem resourceEnvelope_from_source {n : ℕ} (request : BinaryPRGRequest.Request n) (indexWidth N : ℕ) :
    BinaryPRGWordControllerResourceWork.initialBound n request.source.normalizedInput.latticeDenominator indexWidth N ≤
      resourceEnvelope n (request.source.originalInputWordWidth + 1) indexWidth N := by
  have hWidth : binaryWordWidth request.source.normalizedInput.latticeDenominator ≤ request.source.originalInputWordWidth + 1 :=
    request.source.normalized_lattice_wordWidth_original.trans (by omega)
  simp only [BinaryPRGWordControllerResourceWork.initialBound, BinaryPRGWordControllerResourceWork.bound,
    BinaryPRGWordControllerResourceWork.pairBound, BinaryPRGWordControllerResourceWork.preparationBound,
    BinaryPRGWordControllerResourceWork.selectedBound, BinaryPRGWordControllerResource.bodyBound,
    resourceEnvelope, BinaryWordIndexCoinController.allowance]
  unfold_boolean_resource_envelope
  simp only [BinaryPRGWordControllerResource.bodyBound,BinaryWordIndexCoinController.allowance,Nat.add_assoc]
  gcongr

macro "unfold_controller_source_envelope" : tactic => `(tactic|
  simp only [BinaryPRGWordControllerTerminalWork.bound, BinaryPRGWordControllerGroupWork.uniformBound,
    BinaryPRGWordControllerGroupWork.mixedBound, BinaryPRGWordControllerFourWork.restoredBound,
    BinaryPRGWordControllerFourWork.runBound, BinaryPRGWordControllerFourWork.gluingBound,
    BinaryPRGWordControllerFourWork.smallBound, BinaryPRGWordControllerFourWork.rootBound,
    BinaryPRGWordControllerFourWork.uniformBound, BinaryPRGWordControllerReflectedWork.bound,
    BinaryPRGWordControllerReflectedWork.selectionBound, BinaryPRGWordControllerReflectedWork.profileBound,
    BinaryPRGWordControllerReflectedWork.emissionBound, BinaryPRGWordControllerReflectedSetupWork.bound,
    BinaryPRGWordControllerReflectedSetupWork.extraScaleBound,
    BinaryPRGWordControllerThreeResourceWork.bound, BinaryPRGWordControllerThreeResourceWork.pairBound,
    BinaryPRGWordControllerThreeResourceWork.preparationBound, BinaryPRGWordControllerThreeResourceWork.selectedBound,
    BinaryThreeResourceExecution.pairBound, BinaryThreeResourceExecution.selectBound,
    BinaryPRGWordControllerThreeResource.bodyBound, BinaryThreeResourceHeight.coinWidth,
    BinaryThreeResourceHeight.resourceHeight, BinaryPRGWordControllerWork.segmentBound,
    BinaryPRGWordControllerWork.pointBound, BinaryPRGWordControllerWork.selectionBound,
    BinaryQuadraticExpression.uniformPrice, BinaryWordIndexCoinController.allowance])

theorem terminal_bound_mono {n m s t K Q indexWidth otherIndexWidth N M : ℕ}
    (hn : n ≤ m) (hs : s ≤ t) (hK : K ≤ Q) (hI : indexWidth ≤ otherIndexWidth) (hN : N ≤ M) :
    BinaryPRGWordControllerTerminalWork.bound n s K indexWidth N ≤
      BinaryPRGWordControllerTerminalWork.bound m t Q otherIndexWidth M := by
  unfold_controller_source_envelope
  unfold_boolean_three_envelope
  unfold_terminal_envelope
  gcongr

def bodyEnvelope (t : ℕ) : ℕ := resourceEnvelope t (8 * t) (3016 * t) (3015 * t) +
  BinaryPRGWordControllerRequestWork.prefixBound t (8 * t) (32 * t) +
    BinaryPRGWordControllerTerminalWork.bound t (32 * t) (5 * t) (3016 * t) (3015 * t) + 2 +
      BinaryPRGOutputRun.fallbackBound t (32 * t) + t * (t + 1) + 2 * t + 2

theorem read_bodyBound (frame : List Bool)
    (parsed : (Σ n, BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed) :
    BinaryPRGWordControllerRequestWork.fixedBound parsed.1.2.request parsed.1.2.request.precision
      (binaryWordWidth (coinBitBudget parsed.1.1 parsed.1.2.request.precision))
      (coinBitBudget parsed.1.1 parsed.1.2.request.precision) ≤ bodyEnvelope (frame.length + 1) := by
  let t := frame.length + 1
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed h
  have hW := BinaryPRGFrameCostJoin.read_source_width frame parsed h
  have hnT : parsed.1.1 ≤ t := by dsimp [t]; omega
  have hKT : parsed.1.2.request.precision ≤ 5 * t := by dsimp [t]; omega
  have hWT : parsed.1.2.request.source.originalInputWordWidth + 1 ≤ 8 * t := by dsimp [t]; omega
  have hN : coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤ 3015 * t := by
    unfold coinBitBudget
    dsimp [t]
    omega
  have hIndex : binaryWordWidth (coinBitBudget parsed.1.1 parsed.1.2.request.precision) ≤ 3016 * t := by
    unfold binaryWordWidth
    have hl := (Nat.log2_le_self (coinBitBudget parsed.1.1 parsed.1.2.request.precision)).trans hN
    dsimp [t] at hl ⊢
    omega
  have hInput : BinaryCachedGroupInputHeight.inputHeight parsed.1.2.request ≤ 32 * t := by
    unfold BinaryCachedGroupInputHeight.inputHeight
    dsimp [t]
    omega
  have hRequest : BinaryCachedTerminalPrimitiveRun.requestHeight parsed.1.2.request ≤ 32 * t := by
    unfold BinaryCachedTerminalPrimitiveRun.requestHeight
    exact max_le hInput (by dsimp [t]; omega)
  have hResource : BinaryPRGWordControllerResourceWork.initialBound parsed.1.1
      parsed.1.2.request.source.normalizedInput.latticeDenominator
      (binaryWordWidth (coinBitBudget parsed.1.1 parsed.1.2.request.precision))
      (coinBitBudget parsed.1.1 parsed.1.2.request.precision) ≤
      resourceEnvelope t (8 * t) (3016 * t) (3015 * t) := (resourceEnvelope_from_source parsed.1.2.request
    (binaryWordWidth (coinBitBudget parsed.1.1 parsed.1.2.request.precision))
    (coinBitBudget parsed.1.1 parsed.1.2.request.precision)).trans (by
      unfold resourceEnvelope BinaryWordIndexCoinController.allowance
      unfold_boolean_resource_envelope
      gcongr)
  have hPrefix : BinaryPRGWordControllerRequestWork.prefixBound parsed.1.1
      parsed.1.2.request.source.originalInputWordWidth (BinaryCachedGroupInputHeight.inputHeight parsed.1.2.request) ≤
      BinaryPRGWordControllerRequestWork.prefixBound t (8 * t) (32 * t) := by
    unfold BinaryPRGWordControllerRequestWork.prefixBound BinaryPRGWordControllerRouteCopyWork.bound
    gcongr
    omega
  have hTerminal := terminal_bound_mono hnT hRequest hKT hIndex hN
  have hFallback : BinaryPRGOutputRun.fallbackBound parsed.1.1 (BinaryCachedGroupInputHeight.inputHeight parsed.1.2.request) ≤
      BinaryPRGOutputRun.fallbackBound t (32 * t) := by
    unfold BinaryPRGOutputRun.fallbackBound
    gcongr
  have hArray := Nat.mul_le_mul hnT (Nat.add_le_add_right hnT 1)
  unfold BinaryPRGWordControllerRequestWork.fixedBound BinaryPRGWordControllerRequestWork.bound bodyEnvelope
  change _ ≤ resourceEnvelope t (8 * t) (3016 * t) (3015 * t) +
    BinaryPRGWordControllerRequestWork.prefixBound t (8 * t) (32 * t) +
      BinaryPRGWordControllerTerminalWork.bound t (32 * t) (5 * t) (3016 * t) (3015 * t) + 2 +
        BinaryPRGOutputRun.fallbackBound t (32 * t) + t * (t + 1) + 2 * t + 2
  omega

set_option maxHeartbeats 2000000 in
theorem bodyEnvelope_polynomial (t : ℕ) (ht : 1 ≤ t) : bodyEnvelope t ≤ 2^512 * t^4 := by
  have h0 : 1 ≤ t^4 := Nat.one_le_pow 4 t ht
  have h1 : t ≤ t^4 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 1 ≤ 4)
  have h2 : t^2 ≤ t^4 := Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 2 ≤ 4)
  have h3 : t^3 ≤ t^4 := Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 3 ≤ 4)
  unfold bodyEnvelope resourceEnvelope BinaryPRGWordControllerRequestWork.prefixBound
    BinaryPRGWordControllerRouteCopyWork.bound BinaryPRGOutputRun.fallbackBound BinaryWordIndexCoinController.allowance
  unfold_boolean_resource_envelope
  unfold_controller_source_envelope
  unfold_boolean_three_envelope
  unfold_terminal_envelope
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  simp (disch := omega) only [max_eq_left]
  ring_nf
  nlinarith only [h0, h1, h2, h3]

theorem read_outputBound (frame : List Bool)
    (parsed : (Σ n, BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed) :
    outputBound parsed.1.2 ≤ (2^512 + 2^192 + 108547) * (frame.length + 1)^4 := by
  have hBody := (read_bodyBound frame parsed h).trans (bodyEnvelope_polynomial (frame.length + 1) (by omega))
  have hSuffix := (BinaryPRGWordControllerFrameWork.read_suffixBound frame parsed h).trans
    (BinaryPRGWordControllerFrameWork.frameSuffixEnvelope_polynomial frame.length)
  have hN : coinBitBudget parsed.1.1 parsed.1.2.request.precision ≤ 3015 * (frame.length + 1) := by
    have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h
    have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed h
    unfold coinBitBudget
    omega
  have h1 : frame.length + 1 ≤ (frame.length + 1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < frame.length + 1) (by decide : 1 ≤ 4)
  have h0 : 1 ≤ (frame.length + 1)^4 := Nat.one_le_pow 4 _ (by omega)
  have h3 : (frame.length + 1)^3 ≤ (frame.length + 1)^4 :=
    Nat.pow_le_pow_right (by omega : 0 < frame.length + 1) (by decide : 3 ≤ 4)
  have hSuffix' := hSuffix.trans (Nat.mul_le_mul_left (2^192) h3)
  unfold outputBound
  nlinarith only [hBody, hSuffix', hN, h1, h0]

def polynomialBound (length : ℕ) : ℕ := (8623936008 + 2^512 + 2^192 + 108550) * (length + 1)^4

theorem run_polynomial (rich : Bool) (frame seed : List Bool) :
    (BinaryPRGWordControllerRawWork.run rich frame seed).2 ≤ polynomialBound frame.length := by
  have hSetup := BinaryPRGSeedPreparedRun.run_polynomial rich frame seed
  unfold BinaryPRGWordControllerRawWork.run
  dsimp only
  cases hRead : (BinaryPRGAccuracyRulerRequest.read frame).1 with
  | none =>
      simp only
      unfold BinaryPRGSeedPreparedRun.run at hSetup
      simp only [hRead] at hSetup
      simp only [BinaryPRGSeedPreparedRun.Ledger.recorded, BinaryPRGSeedBlocks.Ledger.recorded,
        BinaryPRGSeedPreparedRun.polynomialBound, polynomialBound] at hSetup ⊢
      have h0 : 1 ≤ (frame.length + 1)^4 := Nat.one_le_pow 4 _ (by omega)
      nlinarith only [hSetup, h0]
  | some parsed =>
      simp only
      split
      · rename_i hEmpty
        cases hSeed : (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed).1 with
        | none =>
            simp only
            unfold BinaryPRGSeedPreparedRun.run at hSetup
            simp only [hRead, hEmpty, ite_true, hSeed] at hSetup
            simp only [BinaryPRGSeedPreparedRun.Ledger.recorded, BinaryPRGSeedBlocks.Ledger.recorded,
              BinaryPRGSeedPreparedRun.polynomialBound, polynomialBound] at hSetup ⊢
            have h0 : 1 ≤ (frame.length + 1)^4 := Nat.one_le_pow 4 _ (by omega)
            nlinarith only [hSetup, h0]
        | some tables =>
            simp only
            have hOutput := (outputWithWork_bound parsed.1.2 rich tables).trans (read_outputBound frame parsed hRead)
            unfold BinaryPRGSeedPreparedRun.run at hSetup
            simp only [hRead, hEmpty, ite_true, hSeed] at hSetup
            simp only [BinaryPRGSeedPreparedRun.Ledger.recorded, BinaryPRGSeedBlocks.Ledger.recorded,
              BinaryPRGSeedPreparedRun.polynomialBound, polynomialBound] at hSetup ⊢
            have h0 : 1 ≤ (frame.length + 1)^4 := Nat.one_le_pow 4 _ (by omega)
            nlinarith only [hSetup, hOutput, h0]
      · rename_i hNonempty
        unfold BinaryPRGSeedPreparedRun.run at hSetup
        simp only [hRead, hNonempty, ite_false] at hSetup
        simp only [BinaryPRGSeedPreparedRun.Ledger.recorded, BinaryPRGSeedBlocks.Ledger.recorded,
              BinaryPRGSeedPreparedRun.polynomialBound, polynomialBound] at hSetup ⊢
        have h0 : 1 ≤ (frame.length + 1)^4 := Nat.one_le_pow 4 _ (by omega)
        nlinarith only [hSetup, h0]

end Blotto.BinaryPRGWordControllerRawWorkBound
