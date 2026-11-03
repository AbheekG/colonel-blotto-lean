import Blotto.BinaryUnaryPayloadLifetime
import Blotto.BinaryQuadraticLifetime

/-! Signed canonical word parsing consumes actual paired payload cursors,
the actual denominator scan and quadratic canonicalizer. Every old word and
suffix, including all rejection branches, is preserved. Raw frame length
bounds retained cells/activations without a decoded-width oracle. -/
namespace Blotto.BinaryCanonicalFrameLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def readWithTrace (frame : List Bool) : Option ({word : SignedWord // CanonicalWord word} × List Bool) × Trace :=
  match frame with
  | [] => (none,wrap 8 1 [])
  | negative::rest =>
      let first := BinaryUnaryPayloadLifetime.readWithTrace rest
      match first.1 with
      | none => (none,wrap 16 2 [first.2])
      | some numerator =>
          let second := BinaryUnaryPayloadLifetime.readWithTrace numerator.2
          match second.1 with
          | none => (none,wrap 24 2 [first.2,second.2])
          | some denominator =>
              let tested := BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1
              if hDen : tested.1 = true then
                let raw : SignedWord := ⟨negative,numerator.1,denominator.1⟩
                let normalized := BinaryQuadraticLifetime.canonicalizeWithTrace raw
                have hValid : Valid raw := (BinaryEuclideanGCD.nonzero_true_iff _).mp
                  ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases denominator.1).symm.trans hDen)
                have hC : CanonicalWord normalized.1 := by
                  rw [BinaryQuadraticLifetime.canonicalizeWithTrace_state raw hValid]
                  exact fromPayload_canonical negative numerator.1 denominator.1 hValid
                (some (⟨normalized.1,hC⟩,denominator.2),wrap 64 2 [first.2,second.2,tested.2,normalized.2])
              else (none,wrap 32 2 [first.2,second.2,tested.2])

theorem readWithTrace_state (frame : List Bool) : (readWithTrace frame).1 = (BinaryCanonicalFrameWork.read frame).1 := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      unfold readWithTrace BinaryCanonicalFrameWork.read
      dsimp only
      rw [BinaryUnaryPayloadLifetime.readWithTrace_state]
      cases hn : PositiveBinaryWord.readPayload rest with
      | none => rfl
      | some numerator =>
          dsimp only
          rw [BinaryUnaryPayloadLifetime.readWithTrace_state]
          cases hd : PositiveBinaryWord.readPayload numerator.2 with
          | none => rfl
          | some denominator =>
              dsimp only
              by_cases hDen : BinaryEuclideanGCD.nonzero denominator.1 = true
              · have hNew := (BinaryBooleanPrimitiveLifetime.scanWithTrace_erases denominator.1).trans hDen
                rw [dite_eq_left hNew,dite_eq_left hDen]
                apply congrArg some
                apply Prod.ext
                · apply Subtype.ext
                  change (BinaryQuadraticLifetime.canonicalizeWithTrace
                    (⟨negative,numerator.1,denominator.1⟩ : SignedWord)).1 =
                    (canonicalizeWithWork (⟨negative,numerator.1,denominator.1⟩ : SignedWord)).1
                  rw [BinaryQuadraticLifetime.canonicalizeWithTrace_state _ ((BinaryEuclideanGCD.nonzero_true_iff _).mp hDen),
                    canonicalizeWithWork_state]
                · rfl
              · have hNew : ¬ (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).1 = true :=
                  fun h => hDen ((BinaryBooleanPrimitiveLifetime.scanWithTrace_erases denominator.1).symm.trans h)
                rw [dite_eq_right hNew,dite_eq_right hDen]

theorem readWithTrace_canonical_state (frame : List Bool) :
    (readWithTrace frame).1 = BinaryPRGFrame.readCanonical frame :=
  (readWithTrace_state frame).trans (BinaryCanonicalFrameWork.read_state frame)

theorem read_suffix_lt (frame : List Bool) (parsed : {word : SignedWord // CanonicalWord word} × List Bool)
    (h : (readWithTrace frame).1 = some parsed) : parsed.2.length < frame.length :=
  BinaryCanonicalFrameWork.read_suffix_lt frame parsed ((readWithTrace_state frame).symm.trans h)

def envelope (length : ℕ) : ℕ := 3000*(length+2)^3+400*(length+2)

theorem envelope_mono {a b : ℕ} (h : a ≤ b) : envelope a ≤ envelope b := by unfold envelope; gcongr

theorem readWithTrace_usage (frame : List Bool) : usage (readWithTrace frame).2 ≤ envelope frame.length := by
  cases frame with
  | nil => exact (wrap_usage 8 1 []).trans (by simp [envelope])
  | cons negative rest =>
      have hFirst := BinaryUnaryPayloadLifetime.readWithTrace_usage rest
      unfold readWithTrace
      dsimp only
      split
      · have hw := wrap_usage 16 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 16 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2]) ≤ _
        simp only [List.length_cons]
        unfold envelope
        omega
      · rename_i numerator hn
        have hN := BinaryUnaryPayloadLifetime.read_payload_length rest numerator hn
        have hTail := BinaryUnaryPayloadLifetime.read_suffix_lt rest numerator hn
        have hSecond := BinaryUnaryPayloadLifetime.readWithTrace_usage numerator.2
        split
        · have hw := wrap_usage 24 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
            (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          change usage (wrap 24 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
            (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2]) ≤ _
          simp only [List.length_cons]
          unfold envelope
          omega
        · rename_i denominator hd
          have hD := BinaryUnaryPayloadLifetime.read_payload_length numerator.2 denominator hd
          have hScan := BinaryBooleanPrimitiveLifetime.scanWithTrace_bounds denominator.1
          have hS : usage (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).2 ≤ 5*(rest.length+1) := by
            unfold usage BinaryPRGHeapPrimitiveLifetime.cells
            omega
          split
          · have hNorm := BinaryQuadraticLifetime.canonicalizeWithTrace_bounds (⟨negative,numerator.1,denominator.1⟩ : SignedWord)
            have hW : width (⟨negative,numerator.1,denominator.1⟩ : SignedWord) ≤ rest.length := by
              change max numerator.1.length denominator.1.length ≤ rest.length
              exact max_le hN (hD.trans hTail.le)
            have hPow := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left (Nat.add_le_add_right hW 2) 3)
            have hNormUsage : usage (BinaryQuadraticLifetime.canonicalizeWithTrace (⟨negative,numerator.1,denominator.1⟩ : SignedWord)).2 ≤
                3000*(rest.length+2)^3+6*rest.length+28 := by
              unfold usage BinaryPRGHeapPrimitiveLifetime.cells
              omega
            have hw := wrap_usage 64 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
              (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2,
              (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).2,
              (BinaryQuadraticLifetime.canonicalizeWithTrace (⟨negative,numerator.1,denominator.1⟩ : SignedWord)).2]
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
            change usage (wrap 64 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
              (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2,
              (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).2,
              (BinaryQuadraticLifetime.canonicalizeWithTrace (⟨negative,numerator.1,denominator.1⟩ : SignedWord)).2]) ≤ _
            have hE := envelope_mono (show rest.length ≤ (negative::rest).length by simp)
            unfold envelope at hE ⊢
            omega
          · have hw := wrap_usage 32 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
              (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2,
              (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).2]
            simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
            change usage (wrap 32 2 [(BinaryUnaryPayloadLifetime.readWithTrace rest).2,
              (BinaryUnaryPayloadLifetime.readWithTrace numerator.2).2,
              (BinaryBooleanPrimitiveLifetime.scanWithTrace denominator.1).2]) ≤ _
            simp only [List.length_cons]
            unfold envelope
            omega

theorem all_prefix (frame : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length) (readWithTrace frame).2 steps ≤ borrowed+frame.length+envelope frame.length ∧
    framePeak ((readWithTrace frame).2.take steps) ≤ envelope frame.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (readWithTrace_usage frame) _ steps

end Blotto.BinaryCanonicalFrameLifetime
