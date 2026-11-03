import Blotto.BinaryAccuracyWords

/-! Direct word parsing has the same accepted numeric accuracy inputs and
trailing suffixes as the reference reader, including leading-zero payloads. -/

namespace Blotto.BinaryAccuracyWords

theorem read_sound (frame suffix : List Bool) (w : BinaryAccuracyWords) (h : read frame = some (w, suffix)) :
    BinaryAccuracyFrame.read frame = some (w.numeric, suffix) := by
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
      have hnNat := PositiveBinaryWord.read_sound frame rest num hn
      have hdNat := PositiveBinaryWord.read_sound rest tail den hd
      simp only [BinaryAccuracyFrame.read, hnNat, Option.bind_some, hdNat]
      rw [dite_eq_left (show 0 < num.value ∧ 0 < den.value from ⟨num.value_pos, den.value_pos⟩)]
      rfl

theorem read_complete (frame suffix : List Bool) (a : BinaryAccuracyInput)
    (h : BinaryAccuracyFrame.read frame = some (a, suffix)) :
    ∃ w, read frame = some (w, suffix) ∧ w.numeric = a := by
  unfold BinaryAccuracyFrame.read at h
  cases hn : BinaryNatFrame.read frame with
  | none => rw [hn] at h; cases h
  | some first =>
    rcases first with ⟨num, rest⟩
    rw [hn, Option.bind_some] at h
    cases hd : BinaryNatFrame.read rest with
    | none => rw [hd] at h; cases h
    | some second =>
      rcases second with ⟨den, tail⟩
      rw [hd, Option.bind_some] at h
      split at h
      · rename_i hPositive
        rcases PositiveBinaryWord.read_complete frame rest num hPositive.1 hn with ⟨nw, hnWord, hNum⟩
        rcases PositiveBinaryWord.read_complete rest tail den hPositive.2 hd with ⟨dw, hdWord, hDen⟩
        have hPair := Option.some.inj h
        have hAccuracy : (⟨num, den, hPositive.1, hPositive.2⟩ : BinaryAccuracyInput) = a := (Prod.mk.inj hPair).1
        have hTail : tail = suffix := (Prod.mk.inj hPair).2
        refine ⟨⟨nw, dw⟩, ?_, ?_⟩
        · simp only [read, hnWord, Option.bind_some, hdWord, Option.map_some, hTail]
        · apply Eq.trans _ hAccuracy
          exact BinaryAccuracyInput.eq_of_words _ _ hNum hDen
      · cases h

theorem read_numeric_eq (frame : List Bool) :
    (read frame).map (fun parsed => (parsed.1.numeric, parsed.2)) = BinaryAccuracyFrame.read frame := by
  cases hw : read frame with
  | none =>
    cases ha : BinaryAccuracyFrame.read frame with
    | none => rfl
    | some parsed =>
      rcases parsed with ⟨a, suffix⟩
      rcases read_complete frame suffix a ha with ⟨w, hRead, _⟩
      rw [hw] at hRead
      cases hRead
  | some parsed =>
    rcases parsed with ⟨w, suffix⟩
    simp only [Option.map_some]
    exact (read_sound frame suffix w hw).symm

end Blotto.BinaryAccuracyWords
