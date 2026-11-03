import Blotto.BinaryWordObjectArrayAccess
import Blotto.BinaryWordObjectArrayLifetime
import Blotto.BooleanArrayIndexEnumeration
import Blotto.BinaryTapeFrameLifetime
import Blotto.BinaryQuadraticOutputLifetime

/-! Original-budget scaling and framing now consume actual heap/slot-array
reads at Boolean carry-produced indices. No native output array or Fin-index
callback is executed by this suffix. Logical rows are proof interpretation. -/
namespace Blotto.BinaryPhysicalRowOutput
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryWordObjectArray
set_option maxHeartbeats 3000000

def emitWithTrace {n : ℕ} (store : Store n) (budget : SignedWord) : List (List Bool) → Option (List Bool) × Trace
  | [] => (some [],wrap 16 1 [])
  | index::indices =>
      let read := BinaryWordObjectArrayAccess.getWithTrace store index
      match read.1 with
      | none => (none,wrap 24 2 [read.2])
      | some word =>
          let scaled := BinaryQuadraticLifetime.applyWithTrace .mul budget word
          let framed := BinaryTapeFrameLifetime.wordWithTrace scaled.1
          let later := emitWithTrace store budget indices
          match later.1 with
          | none => (none,wrap 64 2 [read.2,scaled.2,framed.2,later.2])
          | some bytes =>
              let joined := BinaryPRGHeapPrimitiveLifetime.appendWithTrace framed.1 bytes
              (some joined.1,wrap 64 2 [read.2,scaled.2,framed.2,later.2,joined.2])

def scaledWords (budget : SignedWord) (words : List SignedWord) : List SignedWord :=
  words.map (BinaryQuadraticData.apply .mul budget)

theorem emit_state {n : ℕ} (store : Store n) (budget : SignedWord) (indices : List (List Bool)) :
    (emitWithTrace store budget indices).1 =
      (indices.mapM (get store)).map (fun words => BinaryStoredRowFrame.words (scaledWords budget words)) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [emitWithTrace]
      dsimp only
      rw [BinaryWordObjectArrayAccess.get_state,getWithWork_state]
      cases hRead : get store index with
      | none => simp [List.mapM_cons,hRead]
      | some word =>
          rw [ih]
          cases hLater : indices.mapM (get store) with
          | none => simp [List.mapM_cons,hRead,hLater]
          | some words =>
              simp [List.mapM_cons,hRead,hLater,scaledWords,BinaryStoredRowFrame.words,
                BinaryPRGHeapPrimitiveLifetime.appendWithTrace_erasure,BinaryPRGWordStoreHeapMachine.appendWithWork_erasure,
                BinaryTapeFrameLifetime.word_state,BinaryTapeFrameLifetime.word_work_state,
                BinaryQuadraticLifetime.applyWithTrace_erases]

theorem gather_range (words : List SignedWord) : ((List.range words.length).mapM (fun i => words[i]?)) = some words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp only [List.length_cons,List.range_succ_eq_map,List.mapM_cons,List.getElem?_cons_zero,
        List.mapM_map,Function.comp_def,List.getElem?_cons_succ,ih]
      rfl

theorem gather_enumerate {n : ℕ} (store : Store n) (words : List SignedWord) (h : store.Realizes words) :
    ((BooleanArrayIndexEnumeration.enumerateWithTrace words).1.mapM (get store)) = some words := by
  have hGet : get store = fun index => words[BinaryCarryCounter.value index]? := by
    funext index
    exact get_state store words h index
  rw [hGet]
  change List.mapM ((fun i => words[i]?) ∘ BinaryCarryCounter.value)
    (BooleanArrayIndexEnumeration.enumerateWithTrace words).1 = some words
  rw [← List.mapM_map,BooleanArrayIndexEnumeration.enumerate_values]
  exact gather_range words

theorem emit_enumerate {n : ℕ} (store : Store n) (words : List SignedWord) (h : store.Realizes words) (budget : SignedWord) :
    (emitWithTrace store budget (BooleanArrayIndexEnumeration.enumerateWithTrace words).1).1 =
      some (BinaryStoredRowFrame.words (scaledWords budget words)) := by
  rw [emit_state,gather_enumerate store words h]
  rfl

theorem scaled_width (budget word : SignedWord) (hB : BinaryRationalOpcode.Valid budget) (hW : BinaryRationalOpcode.Valid word)
    (W : ℕ) (hBW : width budget ≤ W) (hWW : width word ≤ W) :
    width (BinaryQuadraticData.apply .mul budget word) ≤ 3*W+1 := by
  rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state .mul budget word hB hW]
  exact (BinaryPRGPreparationWork.apply_stored_width .mul budget word).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (max_le hBW hWW)) 1)

def stepEnvelope {n : ℕ} (store : Store n) (I W : ℕ) : ℕ :=
  BinaryWordObjectArrayAccess.envelope store I+BinaryQuadraticLifetime.opcodeBound W+BinaryQuadraticLifetime.opcodeFrames W+
    1024*(3*W+2)+128*(12*W+8)+256

theorem emit_usage {n : ℕ} (store : Store n) (words : List SignedWord) (hStore : store.Realizes words)
    (budget : SignedWord) (hBV : BinaryRationalOpcode.Valid budget) (I W : ℕ)
    (hB : width budget ≤ W) (hWords : ∀ word ∈ words,BinaryRationalOpcode.Valid word ∧ width word ≤ W)
    (indices : List (List Bool)) (hIndices : ∀ index ∈ indices,index.length ≤ I) :
    usage (emitWithTrace store budget indices).2 ≤ indices.length*stepEnvelope store I W+32 := by
  induction indices with
  | nil => exact (wrap_usage 16 1 []).trans (by simp)
  | cons index indices ih =>
      have hi := hIndices index (by simp)
      have hRest := ih (fun i hm => hIndices i (by simp [hm]))
      have hRead := BinaryWordObjectArrayAccess.get_usage store index
      have hRead' : usage (BinaryWordObjectArrayAccess.getWithTrace store index).2 ≤ BinaryWordObjectArrayAccess.envelope store I := by
        apply hRead.trans
        unfold BinaryWordObjectArrayAccess.envelope BinaryReferenceVector.readBound
        gcongr
      rw [emitWithTrace]
      dsimp only
      cases hGot : (BinaryWordObjectArrayAccess.getWithTrace store index).1 with
      | none =>
          have hw := wrap_usage 24 2 [(BinaryWordObjectArrayAccess.getWithTrace store index).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          simp only [List.length_cons]
          unfold stepEnvelope
          nlinarith
      | some word =>
          have hWord : word ∈ words := by
            rw [BinaryWordObjectArrayAccess.get_realizes store words hStore] at hGot
            exact getElemOption_mem _ _ _ hGot
          obtain ⟨hValid,hWidth⟩ := hWords word hWord
          have hScaled := BinaryQuadraticLifetime.applyWithTrace_bounds .mul budget word W hB hWidth
          have hScaleUsage : usage (BinaryQuadraticLifetime.applyWithTrace .mul budget word).2 ≤
              BinaryQuadraticLifetime.opcodeBound W+BinaryQuadraticLifetime.opcodeFrames W := by
            unfold usage BinaryPRGHeapPrimitiveLifetime.cells
            exact Nat.add_le_add hScaled.1 hScaled.2
          have hNewWidth : width (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1 ≤ 3*W+1 := by
            rw [BinaryQuadraticLifetime.applyWithTrace_erases]
            exact scaled_width budget word hBV hValid W hB hWidth
          have hf := BinaryTapeFrameLifetime.word_usage (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1
          have hl := BinaryTapeFrameLifetime.word_length (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1
          have ha := BinaryReferenceVectorLifetime.append_usage
            (BinaryTapeFrameLifetime.wordWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1).1
            ((emitWithTrace store budget indices).1.getD [])
          cases hLater : (emitWithTrace store budget indices).1 with
          | none =>
              have hw := wrap_usage 64 2 [(BinaryWordObjectArrayAccess.getWithTrace store index).2,
                (BinaryQuadraticLifetime.applyWithTrace .mul budget word).2,
                (BinaryTapeFrameLifetime.wordWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1).2,
                (emitWithTrace store budget indices).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              simp only [List.length_cons]
              unfold stepEnvelope at *
              nlinarith
          | some bytes =>
              rw [hLater,Option.getD_some] at ha
              have hw := wrap_usage 64 2 [(BinaryWordObjectArrayAccess.getWithTrace store index).2,
                (BinaryQuadraticLifetime.applyWithTrace .mul budget word).2,
                (BinaryTapeFrameLifetime.wordWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1).2,
                (emitWithTrace store budget indices).2,
                (BinaryPRGHeapPrimitiveLifetime.appendWithTrace
                  (BinaryTapeFrameLifetime.wordWithTrace (BinaryQuadraticLifetime.applyWithTrace .mul budget word).1).1 bytes).2]
              simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
              simp only [List.length_cons]
              unfold stepEnvelope at *
              nlinarith

end Blotto.BinaryPhysicalRowOutput
