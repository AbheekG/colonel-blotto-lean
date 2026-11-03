import Blotto.BinaryPRGHeaderFrame
import Blotto.UnaryPayloadWork

/-! Actual signed game-frame reads retain unary payloads and one native
canonicalization. Malformed/truncated/zero-denominator paths preserve old
rejection. Primitive normalization and Boolean/cell visits derive from the
actual frame length; integer/controller/address/physical costs are separate. -/

namespace Blotto.BinaryCanonicalFrameWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode

structure Ledger where
  framing : ℕ
  normalization : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.framing + ledger.normalization

theorem payload_suffix_lt (frame payload suffix : List Bool)
    (h : PositiveBinaryWord.readPayload frame = some (payload,suffix)) : suffix.length < frame.length := by
  rw [PositiveBinaryWord.readPayload_refines] at h
  unfold PositiveBinaryWord.readPayloadNumeric at h
  cases hs : BinaryNatFrame.scanWidth 0 frame with
  | none => rw [hs,Option.bind_none] at h; cases h
  | some pair =>
      rcases pair with ⟨count,rest⟩
      rw [hs,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        have hl := BinaryNatFrame.scanWidth_length 0 frame count rest hs
        simp only [List.length_drop]
        omega
      · cases h

def read (frame : List Bool) : Option ({word : SignedWord // CanonicalWord word} × List Bool) × Ledger :=
  match frame with
  | [] => (none,⟨1,0⟩)
  | negative :: rest =>
      let first := PositiveBinaryWord.readPayload rest
      let firstWork := 1 + UnaryPayload.readSteps rest
      match first with
      | none => (none,⟨firstWork,0⟩)
      | some numerator =>
          let second := PositiveBinaryWord.readPayload numerator.2
          let framing := firstWork + UnaryPayload.readSteps numerator.2
          match second with
          | none => (none,⟨framing,0⟩)
          | some denominator =>
              let visits := framing + denominator.1.length + 1
              if hDen : BinaryEuclideanGCD.nonzero denominator.1 = true then
                let raw : SignedWord := ⟨negative,numerator.1,denominator.1⟩
                let normalized := canonicalizeWithWork raw
                have hC : CanonicalWord normalized.1 := by
                  rw [canonicalizeWithWork_state]
                  exact fromPayload_canonical negative numerator.1 denominator.1 ((BinaryEuclideanGCD.nonzero_true_iff _).mp hDen)
                (some (⟨normalized.1,hC⟩,denominator.2),⟨visits,normalized.2⟩)
              else (none,⟨visits,0⟩)

def forget (parsed : {word : SignedWord // CanonicalWord word} × List Bool) : SignedWord × List Bool := (parsed.1.val,parsed.2)

theorem read_raw_state (frame : List Bool) : (read frame).1.map forget = BinaryRationalEncoding.readFrame frame := by
  cases frame with
  | nil => rfl
  | cons negative rest =>
      unfold read BinaryRationalEncoding.readFrame
      dsimp only
      cases hn : PositiveBinaryWord.readPayload rest with
      | none => rfl
      | some numerator =>
          dsimp only [Option.bind_some]
          cases hd : PositiveBinaryWord.readPayload numerator.2 with
          | none => rfl
          | some denominator =>
              dsimp only [Option.bind_some]
              split
              · rfl
              · rfl

theorem read_state (frame : List Bool) : (read frame).1 = BinaryPRGFrame.readCanonical frame := by
  have hOld : (BinaryPRGFrame.readCanonical frame).map forget = BinaryRationalEncoding.readFrame frame := by
    unfold BinaryPRGFrame.readCanonical
    split
    · rename_i hNone
      exact hNone.symm
    · rename_i parsed hSome
      exact hSome.symm
  have he := (read_raw_state frame).trans hOld.symm
  cases hn : (read frame).1 with
  | none =>
      rw [hn,Option.map_none] at he
      cases ho : BinaryPRGFrame.readCanonical frame with
      | none => rfl
      | some parsed => rw [ho,Option.map_some] at he; cases he
  | some parsed =>
      rw [hn,Option.map_some] at he
      cases ho : BinaryPRGFrame.readCanonical frame with
      | none => rw [ho,Option.map_none] at he; cases he
      | some old =>
          rw [ho,Option.map_some] at he
          have hv := Option.some.inj he
          change (parsed.1.val,parsed.2) = (old.1.val,old.2) at hv
          have hw : parsed.1.val = old.1.val := congrArg (fun pair : SignedWord × List Bool => pair.1) hv
          have ht : parsed.2 = old.2 := congrArg (fun pair : SignedWord × List Bool => pair.2) hv
          have hp : parsed = old := Prod.ext (Subtype.ext hw) ht
          exact congrArg some hp

theorem read_framing_bound (frame : List Bool) : (read frame).2.framing ≤ 3 * frame.length + 3 := by
  cases frame with
  | nil => exact Nat.le_add_left _ _
  | cons negative rest =>
      have hFirst := UnaryPayload.readSteps_bound rest
      unfold read
      dsimp only
      split
      · simp only [List.length_cons]; omega
      · rename_i numerator hn
        have hSuffix := payload_suffix_lt rest numerator.1 numerator.2 hn
        have hSecond := UnaryPayload.readSteps_bound numerator.2
        split
        · simp only [List.length_cons]; omega
        · rename_i denominator hd
          have hWidth := BinaryPRGHeaderFrame.readPayload_length_bound numerator.2 denominator.1 denominator.2 hd
          split <;> simp only [List.length_cons] <;> omega

theorem read_normalization_bound (frame : List Bool) : (read frame).2.normalization ≤ 170 * (frame.length + 1) ^ 3 := by
  cases frame with
  | nil => exact Nat.zero_le _
  | cons negative rest =>
      unfold read
      dsimp only
      split
      · exact Nat.zero_le _
      · rename_i numerator hn
        have hN := BinaryPRGHeaderFrame.readPayload_length_bound rest numerator.1 numerator.2 hn
        have hSuffix := payload_suffix_lt rest numerator.1 numerator.2 hn
        split
        · exact Nat.zero_le _
        · rename_i denominator hd
          have hD := BinaryPRGHeaderFrame.readPayload_length_bound numerator.2 denominator.1 denominator.2 hd
          split
          · have hp := canonicalizeWithWork_bound (⟨negative,numerator.1,denominator.1⟩ : SignedWord)
            have hw : width (⟨negative,numerator.1,denominator.1⟩ : SignedWord) + 1 ≤ (negative :: rest).length + 1 := by
              unfold width; simp only [List.length_cons]; omega
            exact hp.trans (Nat.mul_le_mul_left 170 (Nat.pow_le_pow_left hw 3))
          · exact Nat.zero_le _

def bound (length : ℕ) : ℕ := 170 * (length + 1) ^ 3 + 3 * length + 3

theorem read_bound (frame : List Bool) : (read frame).2.recorded ≤ bound frame.length := by
  have hf := read_framing_bound frame
  have hn := read_normalization_bound frame
  unfold Ledger.recorded bound
  omega

theorem bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b := by
  unfold bound
  gcongr

theorem read_suffix_lt (frame : List Bool) (parsed : {word : SignedWord // CanonicalWord word} × List Bool)
    (h : (read frame).1 = some parsed) : parsed.2.length < frame.length := by
  cases frame with
  | nil => cases h
  | cons negative rest =>
      unfold read at h
      dsimp only at h
      split at h
      · cases h
      · rename_i numerator hn
        have hFirst := payload_suffix_lt rest numerator.1 numerator.2 hn
        split at h
        · cases h
        · rename_i denominator hd
          have hSecond := payload_suffix_lt numerator.2 denominator.1 denominator.2 hd
          split at h
          · cases Option.some.inj h
            simp only [List.length_cons]
            omega
          · cases h

end Blotto.BinaryCanonicalFrameWork
