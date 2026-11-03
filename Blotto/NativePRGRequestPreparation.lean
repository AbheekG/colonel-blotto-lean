import Blotto.NativePRGPreparedSampler
import Blotto.BinaryReferenceCheckedPreparation
import Blotto.RationalPRGRequestReadBounds
import Blotto.AccuracyCounterBitCost

/-! The reference-checked game and raw positive accuracy words are parsed
once. Successful preparation stores only game/precision/header, enforces the
complete-request suffix gate, and refines every old seeded byte result. -/

namespace Blotto.NativePRGRequestPreparation
set_option autoImplicit false
set_option maxHeartbeats 2000000

def readWords (bits : List Bool) : Option ((Σ n,RationalPRGOriginalInput n) × BinaryAccuracyWords × List Bool) :=
  (BinaryReferenceCheckedPreparation.checked bits).bind (fun game =>
    (BinaryAccuracyWords.read game.2).map (fun accuracy => (game.1,accuracy.1,accuracy.2)))

theorem readWords_refines (bits : List Bool) : readWords bits = RationalPRGBinaryRequest.readWords bits := by
  simp only [readWords,RationalPRGBinaryRequest.readWords,BinaryReferenceCheckedPreparation.checked_refines,
    BinarySequentialGameFrame.checked_refines]

def prepare (bits : List Bool) : Option (Σ n,NativePRGPreparedSampler.Prepared n) :=
  (readWords bits).bind (fun parsed =>
    if parsed.2.2 = [] then some ⟨parsed.1.1,NativePRGPreparedSampler.ofInput parsed.1.2 parsed.2.1.precision⟩
    else none)

def run (rich : Bool) (request seed : List Bool) : Option (List Bool) :=
  (prepare request).bind (fun prepared =>
    (RationalPRGBinaryRequest.seedTable
      (RationalLottoResourceSystem.sampleBitBudget prepared.1 prepared.2.precision) seed).map
      (fun table => NativePRGPreparedSampler.output prepared.2 rich table.read))

theorem run_refines (rich : Bool) (request seed : List Bool) :
    run rich request seed = RationalPRGBinaryRequest.run rich request seed := by
  unfold run prepare RationalPRGBinaryRequest.run
  rw [Option.bind_assoc,readWords_refines]
  apply congrArg (Option.bind (RationalPRGBinaryRequest.readWords request))
  funext parsed
  by_cases h : parsed.2.2 = []
  · simp only [ite_eq_left h,Option.bind_some,NativePRGPreparedSampler.output_data]
    rfl
  · simp only [ite_eq_right h,Option.bind_none]

theorem prepare_encode {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    prepare (RationalPRGBinaryRequest.encode i a) =
      some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ := by
  obtain ⟨words,hRead,hNumeric⟩ := BinaryAccuracyWords.read_encode_append a []
  have hK : words.precision = a.precision := by rw [words.precision_eq,hNumeric]
  have hGame : BinaryReferenceCheckedPreparation.checked (RationalPRGBinaryRequest.encode i a) =
      some (⟨n,i⟩,BinaryAccuracyFrame.encode a) := by
    simp only [RationalPRGBinaryRequest.encode,BinaryReferenceCheckedPreparation.checked_refines,
      BinarySequentialGameFrame.checked_refines,RationalPRGBinaryInput.readChecked_encode_append]
  simp only [List.append_nil] at hRead
  simp only [prepare,readWords,hGame,Option.bind_some,hRead,Option.map_some,ite_true,hK]

theorem run_encode {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) :
    run rich (RationalPRGBinaryRequest.encode i a) (List.ofFn bits) =
      some (if rich then i.richOutputBits a.precision bits else i.poorOutputBits a.precision bits) := by
  rw [run_refines]
  exact RationalPRGBinaryRequest.run_encode i a rich bits

theorem run_returned_budget {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n a.precision) → Bool) (frame : List Bool)
    (h : run rich (RationalPRGBinaryRequest.encode i a) (List.ofFn bits) = some frame) :
    RationalPRGBinaryRequest.ReturnedBudget n (if rich then i.a else i.b) frame := by
  rw [run_refines] at h
  exact RationalPRGBinaryRequest.run_returned_budget i a rich bits frame h

def readPrecisionWork (model : RationalCostModel) (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  BinaryReferenceCheckedPreparation.work model primitive bits+
    match BinaryReferenceCheckedPreparation.checked bits with
    | none => 0
    | some game => BinaryAccuracyWords.readPrecisionBitWork primitive game.2

theorem read_precision_frame_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (bits : List Bool) :
    readPrecisionWork model primitive bits ≤
      BinarySequentialGameFrame.frameCheckedPrice model c bits.length+
        BinaryReferenceCheckedPreparation.tableBound c bits.length bits.length+
          (127+48*c)*bits.length+634+240*c := by
  have hg := BinaryReferenceCheckedPreparation.work_frame_bound model primitive c hPrimitive bits
  unfold readPrecisionWork
  cases hGame : BinaryReferenceCheckedPreparation.checked bits with
  | none => simp only; omega
  | some game =>
    rcases game with ⟨input,rest⟩
    have hOld : RationalPRGBinaryInput.readChecked bits = some (input,rest) := by
      simpa only [BinaryReferenceCheckedPreparation.checked_refines,BinarySequentialGameFrame.checked_refines] using hGame
    have hSuffix := (RationalPRGBinaryInput.readChecked_bounds bits input rest hOld).2
    have ha := BinaryAccuracyWords.readPrecisionBitWork_bound primitive c hPrimitive rest
    have hm := Nat.mul_le_mul_left (127+48*c) hSuffix
    simp only
    omega

theorem encoded_read_precision_bound {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    let frame := RationalPRGBinaryRequest.encode i a
    readPrecisionWork model primitive frame ≤
      BinarySequentialGameFrame.checkedPrice model c n frame.length+
        BinaryReferenceCheckedPreparation.tableBound c n frame.length+
          (127+48*c)*(BinaryAccuracyFrame.encode a).length+634+240*c := by
  dsimp only
  have hGame := (BinaryReferenceCheckedPreparation.encoded_contract i model primitive c hPrimitive
    (BinaryAccuracyFrame.encode a)).1
  have hWork := (BinaryReferenceCheckedPreparation.encoded_contract i model primitive c hPrimitive
    (BinaryAccuracyFrame.encode a)).2
  have hAccuracy := BinaryAccuracyWords.readPrecisionBitWork_bound primitive c hPrimitive (BinaryAccuracyFrame.encode a)
  change BinaryReferenceCheckedPreparation.checked (RationalPRGBinaryRequest.encode i a) =
    some (⟨n,i⟩,BinaryAccuracyFrame.encode a) at hGame
  change BinaryReferenceCheckedPreparation.work model primitive (RationalPRGBinaryRequest.encode i a) ≤
    BinarySequentialGameFrame.checkedPrice model c n (RationalPRGBinaryRequest.encode i a).length+
      BinaryReferenceCheckedPreparation.tableBound c n (RationalPRGBinaryRequest.encode i a).length at hWork
  unfold readPrecisionWork
  rw [hGame]
  dsimp only
  simpa only [Nat.add_assoc] using Nat.add_le_add hWork hAccuracy

/- Source parsing/recognition/table/accuracy/header components. Descriptor
address/record writes and remaining wrapper/control prices stay separate. -/
def componentWork (model : RationalCostModel) (primitive : ℕ → ℕ) (bits : List Bool) : ℕ :=
  readPrecisionWork model primitive bits+
    match prepare bits with
    | none => 0
    | some prepared => NativePRGPreparedSampler.headerWork primitive prepared.1

def componentBound (model : RationalCostModel) (c count frameLength accuracyLength : ℕ) : ℕ :=
  BinarySequentialGameFrame.checkedPrice model c count frameLength+
    BinaryReferenceCheckedPreparation.tableBound c count frameLength+
      (127+48*c)*accuracyLength+634+240*c+
        (256*(c+1)*(binaryWordWidth count+1)*(binaryWordWidth (binaryWordWidth count+2)+1)+
          6*binaryWordWidth count+5)

theorem encoded_preparation_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    let frame := RationalPRGBinaryRequest.encode i a
    prepare frame = some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ ∧
      componentWork model primitive frame ≤ componentBound model c n frame.length (BinaryAccuracyFrame.encode a).length := by
  have hp := prepare_encode i a
  have hr := encoded_read_precision_bound i a model primitive c hPrimitive
  have hh := NativePRGPreparedSampler.header_work_bound primitive c hPrimitive n
  constructor
  · exact hp
  · unfold componentWork
    rw [hp]
    unfold componentBound
    exact Nat.add_le_add hr hh

end Blotto.NativePRGRequestPreparation
