import Blotto.BinaryCanonicalFrameWork

/-! Actual variable-count game-word reading retains each canonicalized word
and follows its returned suffix. Even a huge rejected declared count gets a
frame-length-derived bound: every successful word consumes input before the
recursive call. No numerical-dimension bound or accepted-game promise is
assumed. List/array/controller/bookkeeping/physical costs remain separate. -/

namespace Blotto.BinaryCanonicalRowReadWork
open BinaryRationalNormalization BinaryPRGFrame

def read : (n : ℕ) → List Bool → Option (Words n × List Bool) × ℕ
  | 0,bits => (some (⟨[],rfl,by simp⟩,bits),0)
  | n+1,bits =>
      let first := BinaryCanonicalFrameWork.read bits
      match first.1 with
      | none => (none,first.2.recorded)
      | some parsed =>
          let later := read n parsed.2
          let result := later.1.map (fun rest =>
            (⟨parsed.1.val :: rest.1.row,(by simp [rest.1.length]),
              (by intro word hw; rcases List.mem_cons.mp hw with he | ht
                  · subst word; exact parsed.1.property
                  · exact rest.1.canonical word ht)⟩,rest.2))
          (result,first.2.recorded + later.2)

theorem read_state (n : ℕ) (bits : List Bool) : (read n bits).1 = BinaryPRGFrame.readWords n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
      unfold read BinaryPRGFrame.readWords
      dsimp only
      rw [← BinaryCanonicalFrameWork.read_state bits]
      cases he : (BinaryCanonicalFrameWork.read bits).1 with
      | none => rfl
      | some parsed => simp only [Option.bind_some,ih]

def bound (length : ℕ) : ℕ := (length + 1) * BinaryCanonicalFrameWork.bound length

theorem read_bound (n : ℕ) (bits : List Bool) : (read n bits).2 ≤ bound bits.length := by
  induction n generalizing bits with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hFirst := BinaryCanonicalFrameWork.read_bound bits
      unfold read
      dsimp only
      split
      · exact hFirst.trans (Nat.le_mul_of_pos_left _ (by omega))
      · rename_i parsed hParsed
        have hSize := BinaryCanonicalFrameWork.read_suffix_lt bits parsed hParsed
        have hLater := ih parsed.2
        have hPrice := BinaryCanonicalFrameWork.bound_mono hSize.le
        have hVisits := Nat.mul_le_mul (show parsed.2.length + 1 ≤ bits.length by omega) hPrice
        have hTail := hLater.trans hVisits
        unfold bound
        rw [Nat.add_mul,one_mul]
        omega

theorem bound_mono {a b : ℕ} (h : a ≤ b) : bound a ≤ bound b :=
  Nat.mul_le_mul (Nat.add_le_add_right h 1) (BinaryCanonicalFrameWork.bound_mono h)

end Blotto.BinaryCanonicalRowReadWork
