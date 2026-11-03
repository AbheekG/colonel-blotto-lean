import Blotto.UnaryPayloadWork
import Blotto.BinaryAccuracyTraversal

/-! The primary unary payload path supplies a smaller traversal ledger.
It includes paired-cursor visits, payload cons cells and a trimming pass.
Word-width counters, allocation and physical instruction costs remain separate. -/

namespace Blotto.UnaryPayload

theorem readReversed_length (frame payload suffix : List Bool)
    (h : readReversed frame = some (payload, suffix)) :
    2 * payload.length + suffix.length + 1 = frame.length := by
  have hRef := readReversed_refines frame
  rw [h] at hRef
  cases hp : read frame with
  | none => rw [hp] at hRef; cases hRef
  | some pair =>
    rcases pair with ⟨bits, tail⟩
    rw [hp, Option.map_some] at hRef
    have hPair := Option.some.inj hRef
    have hLength := PositiveBinaryWord.readPayload_length frame bits tail hp
    have hBits : payload = bits.reverse := (Prod.mk.inj hPair).1
    have hTail : suffix = tail := (Prod.mk.inj hPair).2
    simpa only [hBits, hTail, List.length_reverse] using hLength

end Blotto.UnaryPayload
namespace Blotto.PositiveBinaryWord

def unaryReadTraversalWork (frame : List Bool) : ℕ := UnaryPayload.readSteps frame +
  match UnaryPayload.readReversed frame with
  | none => 0
  | some (payload, _) => 2 * payload.length + 1

theorem unaryReadTraversalWork_bound (frame : List Bool) : unaryReadTraversalWork frame ≤ 2 * frame.length + 2 := by
  have hSteps := UnaryPayload.readSteps_bound frame
  unfold unaryReadTraversalWork
  cases h : UnaryPayload.readReversed frame with
  | none => dsimp only; omega
  | some pair =>
    rcases pair with ⟨payload, suffix⟩
    have hLength := UnaryPayload.readReversed_length frame payload suffix h
    change UnaryPayload.readSteps frame + (2 * payload.length + 1) ≤ 2 * frame.length + 2
    omega

end Blotto.PositiveBinaryWord
namespace Blotto.BinaryAccuracyWords

def unaryReadTraversalWork (frame : List Bool) : ℕ := PositiveBinaryWord.unaryReadTraversalWork frame +
  match PositiveBinaryWord.read frame with
  | none => 0
  | some (num, rest) => PositiveBinaryWord.unaryReadTraversalWork rest +
      match PositiveBinaryWord.read rest with
      | none => 0
      | some (den, _) => (BinaryAccuracyWords.mk num den).traversalWork

theorem unaryReadTraversalWork_bound (frame : List Bool) : unaryReadTraversalWork frame ≤ 7 * frame.length + 34 := by
  have hFirst := PositiveBinaryWord.unaryReadTraversalWork_bound frame
  unfold unaryReadTraversalWork
  cases hn : PositiveBinaryWord.read frame with
  | none => dsimp only; omega
  | some first =>
    rcases first with ⟨num, rest⟩
    have hSizeFirst := PositiveBinaryWord.read_width_bound frame rest num hn
    have hSecond := PositiveBinaryWord.unaryReadTraversalWork_bound rest
    dsimp only
    cases hd : PositiveBinaryWord.read rest with
    | none =>
      dsimp only
      simp only [Nat.add_zero]
      omega
    | some second =>
      rcases second with ⟨den, tail⟩
      have hSizeSecond := PositiveBinaryWord.read_width_bound rest tail den hd
      have hPrecision := (BinaryAccuracyWords.mk num den).traversalWork_bound
      change (BinaryAccuracyWords.mk num den).traversalWork ≤ 6 * (num.width + den.width + 5) at hPrecision
      change PositiveBinaryWord.unaryReadTraversalWork frame +
        (PositiveBinaryWord.unaryReadTraversalWork rest + (BinaryAccuracyWords.mk num den).traversalWork) ≤ 7 * frame.length + 34
      omega

end Blotto.BinaryAccuracyWords
