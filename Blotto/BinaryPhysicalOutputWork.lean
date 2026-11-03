import Blotto.BinaryScalarTape
import Blotto.BinaryPhysicalOutputLifetime
import Blotto.BooleanArrayIndexWork
import Blotto.BinaryPRGHeapFixedProperties

/-! Actual measured physical-output execution has the same bytes as the
traced producer. Every lookup, arithmetic call, carry, tape-framing pass and
append has its own reached primitive charge; no callback price is assumed. -/
namespace Blotto.BinaryPhysicalOutputWork
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 4000000

def emitWithWork {n : ℕ} (store : Store n) (budget : SignedWord) : List (List Bool) → Option (List Bool) × ℕ
  | [] => (some [],4)
  | index::indices =>
      let read := getWithWork store index
      match read.1 with
      | none => (none,read.2+8)
      | some word =>
          let scaled := BinaryQuadraticOpcode.applyWithWork .mul budget word
          let framed := BinaryTapeFrameLifetime.wordWithWork scaled.1
          let later := emitWithWork store budget indices
          match later.1 with
          | none => (none,read.2+scaled.2+framed.2+later.2+16)
          | some bytes =>
              let joined := BinaryPRGWordStoreHeapMachine.appendWithWork framed.1 bytes
              (some joined.1,read.2+scaled.2+framed.2+later.2+joined.2.work+16)

theorem emit_state {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emitWithWork store budget indices).1 = (BinaryPhysicalRowOutput.emitWithTrace store budget indices).1 := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [emitWithWork,BinaryPhysicalRowOutput.emitWithTrace]
      dsimp only
      rw [BinaryWordObjectArrayAccess.get_state]
      cases hRead : (getWithWork store index).1 with
      | none => rfl
      | some word =>
          rw [ih]
          cases hLater : (BinaryPhysicalRowOutput.emitWithTrace store budget indices).1 with
          | none => rfl
          | some bytes =>
              simp only [BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,
                BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,BinaryTapeFrameLifetime.word_state,
                BinaryQuadraticLifetime.applyWithTrace_erases,BinaryQuadraticData.apply_erasure]

theorem read_price {n : ℕ} (store : Store n) (I : ℕ) :
    BinaryWordObjectArray.readBound store I ≤ BinaryWordObjectArrayAccess.envelope store I := by
  unfold BinaryWordObjectArray.readBound BinaryWordObjectArrayAccess.envelope BinaryWordObjectArrayAccess.heapReadEnvelope
  omega

theorem emit_work {n : ℕ} (store : Store n) (words : List SignedWord) (hStore : store.Realizes words)
    (budget : SignedWord) (hBV : BinaryRationalOpcode.Valid budget) (I W : ℕ)
    (hB : width budget ≤ W) (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (indices : List (List Bool)) (hIndices : ∀ index ∈ indices,index.length ≤ I) :
    (emitWithWork store budget indices).2 ≤ indices.length*BinaryPhysicalRowOutput.stepEnvelope store I W+32 := by
  induction indices with
  | nil => simp [emitWithWork]
  | cons index indices ih =>
      have hi := hIndices index (by simp)
      have hRest := ih (fun i hm => hIndices i (by simp [hm]))
      have hRead := getWithWork_bound store index
      have hRead' : (getWithWork store index).2 ≤ BinaryWordObjectArrayAccess.envelope store I := by
        apply hRead.trans
        apply (show BinaryWordObjectArray.readBound store index.length ≤ BinaryWordObjectArray.readBound store I by
          unfold BinaryWordObjectArray.readBound BinaryReferenceVector.readBound; gcongr).trans (read_price store I)
      rw [emitWithWork]
      dsimp only
      cases hGot : (getWithWork store index).1 with
      | none =>
          simp only [List.length_cons]
          unfold BinaryPhysicalRowOutput.stepEnvelope
          nlinarith
      | some word =>
          have hWord : word ∈ words := by
            rw [getWithWork_state,get_state store words hStore] at hGot
            exact getElemOption_mem _ _ _ hGot
          obtain ⟨hValid,hWidth⟩ := hWords word hWord
          have hm := BinaryQuadraticOpcode.applyWithWork_bound .mul budget word
          have hPair : BinaryRationalArithmetic.pairWidth budget word ≤ W := max_le hB hWidth
          have hPow := (Nat.pow_le_pow_left (Nat.add_le_add_right hPair 1) 2).trans
            ((Nat.pow_le_pow_left (show W+1 ≤ W+2 by omega) 2).trans
              (Nat.pow_le_pow_right (show 0 < W+2 by omega) (show 2 ≤ 3 by omega)))
          have hScaledWork : (BinaryQuadraticOpcode.applyWithWork .mul budget word).2 ≤ BinaryQuadraticLifetime.opcodeBound W := by
            have hh := Nat.mul_le_mul_left 11000 hPow
            unfold BinaryQuadraticLifetime.opcodeBound
            nlinarith
          have hNewWidth : width (BinaryQuadraticOpcode.applyWithWork .mul budget word).1 ≤ 3*W+1 := by
            rw [BinaryQuadraticData.apply_erasure]
            exact BinaryPhysicalRowOutput.scaled_width budget word hBV hValid W hB hWidth
          have hf := BinaryTapeFrameLifetime.word_work (BinaryQuadraticOpcode.applyWithWork .mul budget word).1
          have hl := BinaryTapeFrameLifetime.word_length (BinaryQuadraticOpcode.applyWithWork .mul budget word).1
          rw [BinaryTapeFrameLifetime.word_state] at hl
          cases hLater : (emitWithWork store budget indices).1 with
          | none =>
              simp only [List.length_cons]
              unfold BinaryPhysicalRowOutput.stepEnvelope at *
              nlinarith
          | some bytes =>
              have ha := (BinaryPRGWordStoreHeapMachine.appendWithWork_price
                (BinaryTapeFrameLifetime.wordWithWork (BinaryQuadraticOpcode.applyWithWork .mul budget word).1).1 bytes).1
              simp only [List.length_cons]
              unfold BinaryPhysicalRowOutput.stepEnvelope at *
              nlinarith

theorem preparation_price (words : List SignedWord) :
    BinaryWordObjectArrayLifetime.workEnvelope words ≤ BinaryWordObjectArrayLifetime.envelope words := by
  unfold BinaryWordObjectArrayLifetime.workEnvelope BinaryWordObjectArrayLifetime.envelope
  nlinarith

def outputWithWork (budget : SignedWord) (header : List Bool) (words : List SignedWord) : List Bool × ℕ :=
  let prepared := BinaryWordObjectArrayLifetime.prepareWithWork words
  let indices := BooleanArrayIndexWork.enumerateWithWork words
  let emitted := emitWithWork prepared.1 budget indices.1
  have hSome : emitted.1.isSome := by
    rw [emit_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,BooleanArrayIndexWork.enumerate_state,
      BinaryPhysicalRowOutput.emit_enumerate _ words (prepare_realizes words) budget]
    rfl
  let joined := BinaryPRGWordStoreHeapMachine.appendWithWork header (emitted.1.get hSome)
  (joined.1,prepared.2+indices.2+emitted.2+joined.2.work+16)

theorem output_state (budget : SignedWord) (header : List Bool) (words : List SignedWord) :
    (outputWithWork budget header words).1 = (BinaryPhysicalOutputLifetime.outputWithTrace budget header words).1 := by
  unfold outputWithWork BinaryPhysicalOutputLifetime.outputWithTrace
  dsimp only
  rw [BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure]
  congr 1
  rw [Option.get_eq_getD (fallback := []),Option.get_eq_getD (fallback := [])]
  rw [emit_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,
    BinaryWordObjectArrayLifetime.prepareWithTrace_state,BooleanArrayIndexWork.enumerate_state]
  rw [BinaryPRGWordStoreHeapMachine.appendWithWork_erasure]

theorem output_work (budget : SignedWord) (header : List Bool) (words : List SignedWord)
    (hBV : BinaryRationalOpcode.Valid budget) (W : ℕ) (hB : width budget ≤ W)
    (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W) :
    (outputWithWork budget header words).2 ≤ BinaryPhysicalOutputLifetime.bound words.length W header.length := by
  have hp := BinaryWordObjectArrayLifetime.prepareWithWork_bound words
  have hpSource := BinaryPhysicalOutputLifetime.preparation_bound words W (fun w hw => (hWords w hw).2)
  have hpEnvelope : BinaryWordObjectArrayLifetime.envelope words ≤ BinaryPhysicalOutputLifetime.preparationBound words.length W := by
    have hPayload := payloadBits_bound words W (fun w hw => (hWords w hw).2)
    have hWidth := (BinaryPhysicalOutputLifetime.wordWidth_le (payloadBits words)).trans (Nat.add_le_add_right hPayload 1)
    unfold BinaryWordObjectArrayLifetime.envelope BinaryPRGWordStoreHeapMachine.allocationBound
      BinaryPhysicalOutputLifetime.preparationBound BinaryPhysicalOutputLifetime.heapCap
    gcongr
  have hPrep := hp.trans ((preparation_price words).trans hpEnvelope)
  have hi := BooleanArrayIndexWork.enumerate_work words
  have he := emit_work (BinaryWordObjectArrayLifetime.prepareWithWork words).1 words
    (by rw [BinaryWordObjectArrayLifetime.prepareWithWork_state]; exact prepare_realizes words)
    budget hBV (binaryWordWidth words.length) W hB hWords (BooleanArrayIndexWork.enumerateWithWork words).1
    (by rw [BooleanArrayIndexWork.enumerate_state]; exact BooleanArrayIndexEnumeration.enumerate_width words)
  have hStep : BinaryPhysicalRowOutput.stepEnvelope (BinaryWordObjectArrayLifetime.prepareWithWork words).1
      (binaryWordWidth words.length) W ≤ BinaryPhysicalOutputLifetime.stepEnvelope words.length W := by
    rw [BinaryWordObjectArrayLifetime.prepareWithWork_state]
    have hRead := BinaryPhysicalOutputLifetime.read_bound words W (fun w hw => (hWords w hw).2)
    rw [BinaryWordObjectArrayLifetime.prepareWithTrace_state] at hRead
    unfold BinaryPhysicalRowOutput.stepEnvelope BinaryPhysicalOutputLifetime.stepEnvelope
    omega
  have hLength : (BooleanArrayIndexWork.enumerateWithWork words).1.length = words.length := by
    rw [BooleanArrayIndexWork.enumerate_state]
    have h := congrArg List.length (BooleanArrayIndexEnumeration.enumerate_values words)
    simpa only [List.length_map,List.length_range] using h
  rw [hLength] at he
  have hEmit := he.trans (Nat.add_le_add_right (Nat.mul_le_mul_left words.length hStep) 32)
  unfold outputWithWork
  dsimp only
  have ha := (BinaryPRGWordStoreHeapMachine.appendWithWork_price header
    ((emitWithWork (BinaryWordObjectArrayLifetime.prepareWithWork words).1 budget
      (BooleanArrayIndexWork.enumerateWithWork words).1).1.get (by
        rw [emit_state,BinaryWordObjectArrayLifetime.prepareWithWork_state,BooleanArrayIndexWork.enumerate_state,
          BinaryPhysicalRowOutput.emit_enumerate _ words (prepare_realizes words) budget]; rfl))).1
  unfold BinaryPhysicalOutputLifetime.bound
  omega

theorem actual_output_work {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n)
    (rich : Bool) (K : ℕ) (outer scalar : BinaryScalarTape K) (header : List Bool) :
    (outputWithWork request.prepared.original.a header
      (BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar).1.1.data.toList).2 ≤
        BinaryPhysicalOutputLifetime.bound n (BinaryPRGHeapFixedProperties.wordWidth request K) header.length := by
  let row := (BinaryPRGHeapFixedLifetime.runWithTrace store request rich K outer scalar).1.1
  have hWords : ∀ word ∈ row.data.toList,BinaryRationalOpcode.Valid word ∧
      width word ≤ BinaryPRGHeapFixedProperties.wordWidth request K := by
    intro word hw
    obtain ⟨i,hi,hValue⟩ := List.mem_iff_getElem.mp hw
    let j : Fin n := ⟨i,by simpa only [Array.length_toList,row.size] using hi⟩
    have hj : row.read j = word := by simpa only [FixedArrayTable.read,Array.getElem_toList] using hValue
    rw [← hj]
    exact ⟨(BinaryPRGHeapFixedLifetime.runWithTrace_canonical store request rich K outer scalar j).1,
      BinaryPRGHeapFixedProperties.row_width store request rich K outer scalar j⟩
  have h := output_work request.prepared.original.a header row.data.toList request.valid.2.1.1.1
    (BinaryPRGHeapFixedProperties.wordWidth request K) (BinaryPRGHeapFixedProperties.scale_width request K) hWords
  simpa only [Array.length_toList,row.size] using h

end Blotto.BinaryPhysicalOutputWork
