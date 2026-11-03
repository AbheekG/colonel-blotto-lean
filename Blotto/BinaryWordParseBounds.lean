import Blotto.BinaryAccuracyWordCorrespondence

/-! Direct word parsing consumes a self-delimiting frame without assembling
its integer. Widths and labelled comparison/shift work are linear in the actual
accuracy frame, including leading-zero and non-minimal payloads. -/

namespace Blotto

namespace BinaryNatFrame

theorem scanWidth_length (count : ℕ) (frame : List Bool) (width : ℕ) (rest : List Bool)
    (h : scanWidth count frame = some (width, rest)) : width + rest.length + 1 = count + frame.length := by
  induction frame generalizing count with
  | nil => cases h
  | cons b tail ih =>
    cases b
    · have ht := ih (count + 1) h
      simp only [List.length_cons]
      omega
    · cases Option.some.inj h
      simp only [List.length_cons]
      omega

end BinaryNatFrame

namespace PositiveBinaryWord

theorem parse_width_bound (bits : List Bool) (w : PositiveBinaryWord) (h : parse bits = some w) :
    w.width ≤ bits.length := by
  have hLength := BinaryBigEndian.trim_length bits
  unfold parse at h
  cases ht : BinaryBigEndian.trim bits with
  | nil => rw [ht] at h; cases h
  | cons head tail =>
    rw [ht] at h hLength
    cases head
    · cases h
    · cases Option.some.inj h
      exact hLength

theorem readPayload_length (frame payload suffix : List Bool) (h : readPayload frame = some (payload, suffix)) :
    2 * payload.length + suffix.length + 1 = frame.length := by
  rw [readPayload_refines] at h
  unfold readPayloadNumeric at h
  cases hs : BinaryNatFrame.scanWidth 0 frame with
  | none => rw [hs] at h; cases h
  | some pair =>
    rcases pair with ⟨width, rest⟩
    rw [hs, Option.bind_some] at h
    split at h
    · rename_i hEnough
      cases Option.some.inj h
      have hLength := BinaryNatFrame.scanWidth_length 0 frame width rest hs
      dsimp only at hEnough hLength ⊢
      simp only [Nat.zero_add] at hLength
      simp only [List.length_take, List.length_drop, Nat.min_eq_left hEnough]
      omega
    · cases h

theorem read_width_bound (frame suffix : List Bool) (w : PositiveBinaryWord) (h : read frame = some (w, suffix)) :
    2 * w.width + suffix.length + 1 ≤ frame.length := by
  rw [read_eq_payload] at h
  cases hp : readPayload frame with
  | none => rw [hp] at h; cases h
  | some pair =>
    rcases pair with ⟨payload, tail⟩
    rw [hp, Option.bind_some] at h
    cases hs : parse payload.reverse with
    | none => rw [hs] at h; cases h
    | some parsed =>
      rw [hs] at h
      cases Option.some.inj h
      have hWidth := parse_width_bound payload.reverse w hs
      have hLength := readPayload_length frame payload tail hp
      simp only [List.length_reverse] at hWidth
      change 2 * w.width + tail.length + 1 ≤ frame.length
      omega

end PositiveBinaryWord

namespace BinaryAccuracyWords

theorem read_width_bound (frame suffix : List Bool) (w : BinaryAccuracyWords) (h : read frame = some (w, suffix)) :
    2 * (w.numerator.width + w.denominator.width) + suffix.length + 2 ≤ frame.length := by
  unfold read at h
  cases hn : PositiveBinaryWord.read frame with
  | none => rw [hn] at h; cases h
  | some first =>
    rcases first with ⟨num, rest⟩
    rw [hn, Option.bind_some] at h
    cases hd : PositiveBinaryWord.read rest with
    | none => rw [hd] at h; cases h
    | some second =>
      rcases second with ⟨den, tail⟩
      rw [hd] at h
      cases Option.some.inj h
      have hnSize := PositiveBinaryWord.read_width_bound frame rest num hn
      have hdSize := PositiveBinaryWord.read_width_bound rest tail den hd
      change 2 * (num.width + den.width) + tail.length + 2 ≤ frame.length
      omega

theorem read_traversalWork_bound (frame suffix : List Bool) (w : BinaryAccuracyWords) (h : read frame = some (w, suffix)) :
    w.traversalWork ≤ 3 * (frame.length - suffix.length) + 24 := by
  have hWidth := read_width_bound frame suffix w h
  have hWork := w.traversalWork_bound
  omega

end BinaryAccuracyWords
end Blotto
