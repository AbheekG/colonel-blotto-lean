import Blotto.SequentialFairPRGSourceLaw

/-! Every encoded legal promised input reaches the actual physical parser.
Acceptance is derived by the exact option-map refinements, without a supplied
acceptance certificate. Costs below keep the encoded input length explicit. -/
namespace Blotto.SequentialFairPRGEncodedInput
open BinarySeedPreparationSpace RationalLottoResourceSystem
open SequentialFairPRGSource SequentialFairPRGSourceContracts
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem logical_encoded {n : ℕ} (input : RationalPRGOriginalInput n) (accuracy : BinaryAccuracyInput) :
    ∃ parsed : Σ m,BinaryPRGAccuracyRulerRequest.Request m,
      (BinaryPRGAccuracyRulerRequest.read (RationalPRGBinaryRequest.encode input accuracy)).1 = some (parsed,[]) ∧
      (BinaryPRGRequest.decoded ⟨parsed.1,parsed.2.request⟩).1 = (⟨n,input⟩ : Σ m,RationalPRGOriginalInput m) ∧
      parsed.2.request.accuracy.numeric = accuracy := by
  obtain ⟨prior,hPrior,hInput,hAccuracy⟩ := BinaryPRGRequest.read_encoded input accuracy []
  simp only [List.append_nil] at hPrior
  have h := BinaryPRGAccuracyRulerRequest.read_state (RationalPRGBinaryRequest.encode input accuracy)
  rw [hPrior] at h
  cases hr : (BinaryPRGAccuracyRulerRequest.read (RationalPRGBinaryRequest.encode input accuracy)).1 with
  | none => rw [hr,Option.map_none] at h; cases h
  | some parsed =>
      rw [hr,Option.map_some] at h
      have he := Option.some.inj h
      have ht := congrArg Prod.snd he
      have hg := congrArg Prod.fst he
      change parsed.2 = [] at ht
      have hp : (⟨parsed.1.1,parsed.1.2.request⟩ : Σ m,BinaryPRGRequest.Request m) = prior := by
        simpa only [BinaryPRGAccuracyRulerRequest.forget] using hg
      refine ⟨parsed.1,?_,?_,?_⟩
      · exact congrArg some (Prod.ext rfl ht)
      · simpa only [hp] using hInput
      · have ha := congrArg (fun p : Σ m,BinaryPRGRequest.Request m => p.2.accuracy.numeric) hp
        exact ha.trans hAccuracy

theorem physical_encoded {n : ℕ} (input : RationalPRGOriginalInput n) (accuracy : BinaryAccuracyInput) :
    ∃ parsed : Σ m,BinaryPRGPhysicalRawRequestLifetime.Request m,
      (BinaryPRGPhysicalRawRequestMeasured.read (RationalPRGBinaryRequest.encode input accuracy)).1.1 = some (parsed,[]) ∧
      (BinaryPRGRequest.decoded ⟨parsed.1,parsed.2.logical.request⟩).1 = (⟨n,input⟩ : Σ m,RationalPRGOriginalInput m) ∧
      parsed.2.logical.request.accuracy.numeric = accuracy := by
  obtain ⟨prior,hPrior,hInput,hAccuracy⟩ := logical_encoded input accuracy
  have h := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original (RationalPRGBinaryRequest.encode input accuracy)
  rw [hPrior] at h
  cases hr : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace (RationalPRGBinaryRequest.encode input accuracy)).1 with
  | none => rw [hr,Option.map_none] at h; cases h
  | some parsed =>
      rw [hr,Option.map_some] at h
      have he := Option.some.inj h
      have ht := congrArg Prod.snd he
      have hg := congrArg Prod.fst he
      change parsed.2 = [] at ht
      have hp : (⟨parsed.1.1,parsed.1.2.logical⟩ : Σ m,BinaryPRGAccuracyRulerRequest.Request m) = prior := by
        simpa only [BinaryPRGPhysicalRawRequestLifetime.forgetParsed] using hg
      refine ⟨parsed.1,?_,?_,?_⟩
      · have hm := congrArg Prod.fst
          (BinaryPRGPhysicalRawRequestMeasured.read_erases (RationalPRGBinaryRequest.encode input accuracy))
        exact hm.trans (hr.trans (congrArg some (Prod.ext rfl ht)))
      · have hd := congrArg (fun p : Σ m,BinaryPRGAccuracyRulerRequest.Request m =>
          (BinaryPRGRequest.decoded ⟨p.1,p.2.request⟩).1) hp
        exact hd.trans hInput
      · have ha := congrArg (fun p : Σ m,BinaryPRGAccuracyRulerRequest.Request m => p.2.request.accuracy.numeric) hp
        exact ha.trans hAccuracy

theorem encoded_length {n : ℕ} (input : RationalPRGOriginalInput n) (accuracy : BinaryAccuracyInput) :
    (RationalPRGBinaryRequest.encode input accuracy).length =
      2*binaryWordWidth n+3+2*input.originalInputWordWidth+n+(BinaryAccuracyFrame.encode accuracy).length := by
  simp only [RationalPRGBinaryRequest.encode,List.length_append,RationalPRGBinaryInput.encode_length]

def dyadicAccuracy (s : ℕ) : BinaryAccuracyInput := ⟨1,2^s,by omega,Nat.two_pow_pos s⟩

theorem dyadic_real (s : ℕ) : (dyadicAccuracy s).real = ((2:ℝ)^s)⁻¹ := by
  simp [dyadicAccuracy,BinaryAccuracyInput.real]

theorem dyadic_frame_length (s : ℕ) : (BinaryAccuracyFrame.encode (dyadicAccuracy s)).length = 2*s+6 := by
  rw [BinaryAccuracyFrame.encode_length]
  simp only [dyadicAccuracy,binaryWordWidth,Nat.log2_two_pow]
  change 2*((0+1)+(s+1))+2 = 2*s+6
  omega

theorem dyadic_precision (s : ℕ) : (dyadicAccuracy s).precision ≤ s+5 := by
  apply binaryRatioPrecision_minimal _ _ (by change 0 < 1; omega)
  change 32*2^s ≤ 1*2^(s+5)
  simp only [pow_add]
  norm_num only [Nat.reducePow]
  omega

def inputSize {n : ℕ} (input : RationalPRGOriginalInput n) (s : ℕ) : ℕ :=
  n+input.originalInputWordWidth+s+binaryWordWidth n+1

theorem dyadic_encoded_length {n : ℕ} (input : RationalPRGOriginalInput n) (s : ℕ) :
    (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)).length =
      2*binaryWordWidth n+2*input.originalInputWordWidth+n+2*s+9 := by
  rw [encoded_length,dyadic_frame_length]
  omega

theorem dyadic_size {n : ℕ} (input : RationalPRGOriginalInput n) (s : ℕ) :
    (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)).length+1 ≤ 10*inputSize input s := by
  rw [dyadic_encoded_length]
  unfold inputSize
  omega

theorem encoded_fair_contract : ∃ C d : ℕ,∀ {n : ℕ} (input : RationalPRGOriginalInput n) (s : ℕ)
    (prices : Representation)
    (bits : Fin (drawCount (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))+
      drawCount (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))) → Bool) (steps : ℕ),
    parsedPairCost (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)) (List.ofFn bits)+
      (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)).length+(List.ofFn bits).length ≤ C*(inputSize input s)^d ∧
    prices.listCellUnits*((RationalPRGBinaryRequest.encode input (dyadicAccuracy s)).length+(List.ofFn bits).length)+
      representedWorkspace prices
        (parsedPair (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)) (List.ofFn bits)).1.1.1.1.1.1.1.1.2 steps ≤
      BinaryCompleteRepresentationSpace.units prices*(C*(inputSize input s)^d) := by
  obtain ⟨C,d,h⟩ := parsedPair_fair_complete
  refine ⟨C*10^d,d,?_⟩
  intro n input s prices bits steps
  have hc := h prices (RationalPRGBinaryRequest.encode input (dyadicAccuracy s)) bits steps
  have hp := Nat.pow_le_pow_left (dyadic_size input s) d
  have hScale : C*((RationalPRGBinaryRequest.encode input (dyadicAccuracy s)).length+1)^d ≤
      (C*10^d)*(inputSize input s)^d := by
    simpa only [mul_pow,Nat.mul_assoc] using Nat.mul_le_mul_left C hp
  exact ⟨hc.1.trans hScale,hc.2.trans (Nat.mul_le_mul_left (BinaryCompleteRepresentationSpace.units prices) hScale)⟩

theorem encoded_laws {n : ℕ} (input : RationalPRGOriginalInput n) (s : ℕ) :
    ∃ parsed : Σ m,BinaryPRGPhysicalRawRequestLifetime.Request m,
      (BinaryPRGPhysicalRawRequestMeasured.read (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))).1.1 = some (parsed,[]) ∧
      (BinaryPRGRequest.decoded ⟨parsed.1,parsed.2.logical.request⟩).1 = (⟨n,input⟩ : Σ m,RationalPRGOriginalInput m) ∧
      parsed.2.logical.request.accuracy.numeric = dyadicAccuracy s ∧
      (SequentialFairPRGSourceLaw.pairLaw (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
        (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) :
        MeasureTheory.Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed).1 ×
          Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed).1)) =
      (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
        (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) true :
        MeasureTheory.Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed).1)).prod
      (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
        (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) false :
        MeasureTheory.Measure (Allocation (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed).1)) ∧
      (regret parsed.2.logical.request.source.realValues (parsed.2.logical.request.source.a : ℝ)
        (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
          (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) true)
        (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
          (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) false) < (dyadicAccuracy s).real ∧
      regret parsed.2.logical.request.source.realValues (parsed.2.logical.request.source.b : ℝ)
        (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
          (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) false)
        (SequentialFairPRGSourceLaw.law (RationalPRGBinaryRequest.encode input (dyadicAccuracy s))
          (BinaryTerminalPhysicalParsedGeneratedLaw.logical parsed) true) < (dyadicAccuracy s).real) := by
  obtain ⟨parsed,hRead,hInput,hAccuracy⟩ := physical_encoded input (dyadicAccuracy s)
  have hLogical := BinaryTerminalPhysicalParsedGeneratedLaw.accepted_logical _ parsed hRead
  have hRegret := SequentialFairPRGSourceLaw.law_regrets _ _ hLogical
  change regret _ _ _ _ < parsed.2.logical.request.accuracy.numeric.real ∧
    regret _ _ _ _ < parsed.2.logical.request.accuracy.numeric.real at hRegret
  rw [hAccuracy] at hRegret
  exact ⟨parsed,hRead,hInput,hAccuracy,SequentialFairPRGSourceLaw.pairLaw_product _ _ hLogical,hRegret⟩

end Blotto.SequentialFairPRGEncodedInput
