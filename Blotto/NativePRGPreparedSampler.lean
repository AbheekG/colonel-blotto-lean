import Blotto.RationalPRGReferenceOutput
import Blotto.PRGAccuracyLogarithm

/-! A native prepared descriptor retains only the checked game, precision
and canonical cached header. Its draws consume an actual stored row once;
raw accuracy words are absent from the draw interface. -/

namespace Blotto.NativePRGPreparedSampler
set_option autoImplicit false

def header (n : ℕ) : List Bool :=
  BinaryLinearRowFrame.payloadInto (BinaryBalancedWordEncoder.bits n) []

theorem header_eq (n : ℕ) : header n = BinaryNatFrame.encode n := by
  simp only [header,BinaryLinearRowFrame.payload_data,BinaryNativeRationalEncoder.payload_bits,List.append_nil]

theorem header_length (n : ℕ) : (header n).length = 2*binaryWordWidth n+1 := by
  rw [header_eq,BinaryNatFrame.encode_length]

def headerWork (primitive : ℕ → ℕ) (n : ℕ) : ℕ :=
  BinaryBalancedWordEncodingCost.bitsWork primitive n+
    (BinaryLinearRowFrame.payloadRun (BinaryBalancedWordEncoder.bits n) []).trace.length

theorem header_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) (n : ℕ) :
    headerWork primitive n ≤ 256*(c+1)*(binaryWordWidth n+1)*
      (binaryWordWidth (binaryWordWidth n+2)+1)+6*binaryWordWidth n+5 := by
  have h := BinaryBalancedWordEncodingCost.bits_work_bound primitive c hPrimitive n
  have hp := (BinaryLinearRowFrame.payload_counts (BinaryBalancedWordEncoder.bits n) []).1
  rw [BinaryBalancedWordEncoder.bits_length] at hp
  unfold headerWork
  omega

structure Prepared (n : ℕ) where
  source : RationalPRGOriginalInput n
  precision : ℕ
  bytes : List Bool
  header_correct : bytes = BinaryNatFrame.encode n

def ofInput {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Prepared n :=
  ⟨i,K,header n,header_eq n⟩

def sample {n : ℕ} (p : Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : RationalResourceArray n :=
  if rich then p.source.storedRichSample p.precision bits else p.source.storedPoorSample p.precision bits

def output {n : ℕ} (p : Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) : List Bool :=
  ReferenceStoredRowFrame.frame p.bytes (sample p rich bits)

theorem sample_fullBudget {n : ℕ} (p : Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    FullBudget (if rich then (p.source.a:ℝ) else (p.source.b:ℝ)) (sample p rich bits).realAllocation := by
  cases rich with
  | false => exact p.source.storedPoorSample_fullBudget p.precision bits
  | true => exact p.source.storedRichSample_fullBudget p.precision bits

theorem output_data {n : ℕ} (p : Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    output p rich bits =
      if rich then p.source.richOutputBits p.precision bits else p.source.poorOutputBits p.precision bits := by
  unfold output sample
  rw [p.header_correct]
  cases rich with
  | false => exact (p.source.referencePoorOutput_data _ _ _).trans (p.source.storedPoorOutput_data _ _)
  | true => exact (p.source.referenceRichOutput_data _ _ _).trans (p.source.storedRichOutput_data _ _)

theorem output_read_budget {n : ℕ} (p : Prepared n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n p.precision) → Bool) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then p.source.a else p.source.b) (output p rich bits) := by
  rw [output_data]
  cases rich with
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    exact ⟨List.ofFn (p.source.poorSample p.precision bits),
      by simpa only [List.append_nil] using p.source.poorOutput_readback p.precision bits [],
      (p.source.output_readback_budgets p.precision bits).2⟩
  | true =>
    simp only [ite_true]
    exact ⟨List.ofFn (p.source.richSample p.precision bits),
      by simpa only [List.append_nil] using p.source.richOutput_readback p.precision bits [],
      (p.source.output_readback_budgets p.precision bits).1⟩

theorem prepared_accuracy_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    regret i.realValues (i.a:ℝ) ((ofInput i a.precision).source.storedRichLaw (ofInput i a.precision).precision)
      ((ofInput i a.precision).source.storedPoorLaw (ofInput i a.precision).precision) < a.real ∧
    regret i.realValues (i.b:ℝ) ((ofInput i a.precision).source.storedPoorLaw (ofInput i a.precision).precision)
      ((ofInput i a.precision).source.storedRichLaw (ofInput i a.precision).precision) < a.real := by
  change regret i.realValues (i.a:ℝ) (i.storedRichLaw a.precision) (i.storedPoorLaw a.precision) < a.real ∧
    regret i.realValues (i.b:ℝ) (i.storedPoorLaw a.precision) (i.storedRichLaw a.precision) < a.real
  rw [i.storedRichLaw_eq,i.storedPoorLaw_eq]
  exact a.original_regrets i

theorem prepared_fair_bit_cap {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    RationalLottoResourceSystem.sampleBitBudget n (ofInput i a.precision).precision ≤
      3*n+5*⌈Real.logb 2 (1/a.real)⌉₊+3025 :=
  a.sampleBitBudget_ceil_bound n

end Blotto.NativePRGPreparedSampler
