import Blotto.BinaryWordParseBounds

/-! Labelled element-traversal work for direct accuracy reading and selection.
The ledger counts fixed list passes and lexicographic visits. It does not assert
integer-counter, allocator or physical bit-machine costs. -/

namespace Blotto.PositiveBinaryWord

def widthVisits : List Bool → ℕ
  | [] => 0
  | true :: _ => 1
  | false :: rest => widthVisits rest + 1

theorem widthVisits_bound (frame : List Bool) : widthVisits frame ≤ frame.length := by
  induction frame with
  | nil => rfl
  | cons b rest ih => cases b <;> simp only [widthVisits, List.length_cons] <;> omega

def readTraversalWork (frame : List Bool) : ℕ :=
  match BinaryNatFrame.scanWidth 0 frame with
  | none => widthVisits frame
  | some (width, rest) => widthVisits frame + rest.length +
      if width ≤ rest.length then 4 * width + 1 else 0

theorem readTraversalWork_bound (frame : List Bool) : readTraversalWork frame ≤ 6 * frame.length + 1 := by
  have hVisits := widthVisits_bound frame
  unfold readTraversalWork
  cases hs : BinaryNatFrame.scanWidth 0 frame with
  | none => dsimp only; omega
  | some pair =>
    rcases pair with ⟨width, rest⟩
    have hLength := BinaryNatFrame.scanWidth_length 0 frame width rest hs
    dsimp only at hLength ⊢
    simp only [Nat.zero_add] at hLength
    split <;> omega

end Blotto.PositiveBinaryWord

namespace Blotto.BinaryAccuracyWords

def readTraversalWork (frame : List Bool) : ℕ :=
  PositiveBinaryWord.readTraversalWork frame +
    match PositiveBinaryWord.read frame with
    | none => 0
    | some (num, rest) => PositiveBinaryWord.readTraversalWork rest +
        match PositiveBinaryWord.read rest with
        | none => 0
        | some (den, _) => (BinaryAccuracyWords.mk num den).traversalWork

theorem readTraversalWork_bound (frame : List Bool) : readTraversalWork frame ≤ 15 * frame.length + 26 := by
  have hFirst := PositiveBinaryWord.readTraversalWork_bound frame
  unfold readTraversalWork
  cases hn : PositiveBinaryWord.read frame with
  | none => dsimp only; omega
  | some first =>
    rcases first with ⟨num, rest⟩
    have hSizeFirst := PositiveBinaryWord.read_width_bound frame rest num hn
    have hSecond := PositiveBinaryWord.readTraversalWork_bound rest
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
      change PositiveBinaryWord.readTraversalWork frame +
        (PositiveBinaryWord.readTraversalWork rest + (BinaryAccuracyWords.mk num den).traversalWork) ≤ 15 * frame.length + 26
      omega

end Blotto.BinaryAccuracyWords
