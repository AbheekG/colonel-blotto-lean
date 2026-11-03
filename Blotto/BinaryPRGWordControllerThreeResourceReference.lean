import Blotto.BinaryPRGWordControllerCategoricalReference
import Blotto.BinarySharedResourceRun

/-! Proof-only complete-coin decomposition of the retained resource controller.
Completed coins resume the actual selected Certified state, at their exact
absolute returned position and under the original shared seed cap. -/

namespace Blotto.BinaryPRGWordControllerThreeResourceReference
open BinaryRationalNormalization BinaryRationalEncoding BinaryThreeResourcePair BinaryResourceChoice
variable {capacity : FixedArrayTable 3 SignedWord} {hC : ∀ j,CanonicalWord (capacity.read j)}

def resume (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (result : Option Bool × ℕ) (hp : result.2 ≤ N) : Option (Certified capacity) × ℕ :=
  match result.1 with
  | none => (none,result.2)
  | some branch => BinarySharedResourceRun.runIndexed (hC := hC) N bits (.ready (choice.select branch)) result.2 hp

theorem resume_congr (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (first second : Option Bool × ℕ) (hFirst : first.2 ≤ N) (hSecond : second.2 ≤ N) (h : first = second) :
    resume N bits choice first hFirst = resume N bits choice second hSecond := by
  cases h
  rfl

theorem coin_compose {width : ℕ} (N : ℕ) (bits : Fin N → Bool)
    (choice : Choice capacity hC) (a b : FixedBinaryWord width) (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (pos : ℕ) (hp : pos ≤ N) :
    BinarySharedResourceRun.runIndexed N bits (.coin choice a b hb hab) pos hp =
      resume N bits choice (BinaryStoredCoinIndexed.run N bits a b pos hp)
        (BinaryPRGWordControllerCategoricalReference.coin_position N bits a b pos hp).2 := by
  conv_lhs => unfold BinarySharedResourceRun.runIndexed
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  by_cases hz : a.isZero = true
  · simp only [hz,ite_true,dite_true,resume]
  · simp only [hz,Bool.false_eq_true,ite_false,dite_false]
    by_cases he : a.same b = true
    · simp only [he,ite_true,dite_true,resume]
    · simp only [he,Bool.false_eq_true,ite_false,dite_false]
      by_cases hr : pos < N
      · simp only [dite_eq_left hr]
        by_cases hd : bits ⟨pos,hr⟩ = (a.coinStep b).1
        · simp only [hd,ite_true]
          exact coin_compose N bits choice (a.coinStep b).2 b hb
            (a.coinStep_normalized b (by
              have hn : a.value ≠ b.value := fun h => he ((a.same_value b).mpr h)
              omega)).le (pos + 1) (by omega)
        · simp only [hd,ite_false,resume]
      · simp only [dite_eq_right hr,resume]
termination_by N - pos

theorem pending_compose (N : ℕ) (bits : Fin N → Bool) (choice : Choice capacity hC)
    (pos : ℕ) (hp : pos ≤ N) :
    BinarySharedResourceRun.runIndexed N bits (BinarySharedResourceRun.pending choice) pos hp =
      resume N bits choice (BinaryStoredCoinIndexed.sample choice.probability N bits pos hp)
        (BinaryPRGWordControllerCategoricalReference.coin_position N bits
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).1
          (BinaryStoredRationalCoin.fromStored choice.probability.numerator choice.probability.denominator).2 pos hp).2 := by
  unfold BinarySharedResourceRun.pending BinaryStoredCoinIndexed.sample
  apply coin_compose

theorem prepared_state (state : Certified capacity) (choice : Choice capacity hC)
    (h : BinaryResourceChoice.prepare capacity hC state = .ask choice) : choice.state = state := by
  unfold BinaryResourceChoice.prepare at h
  split at h
  · cases Preparation.ask.inj h
    rfl
  · cases h


/-- Proof-only offset simulation. Concrete inputWindow instantiates the reader
agreement below directly; the data-only Boolean controller receives no oracle. -/
theorem runIndexed_offset (N M base : ℕ) (hSize : N = base + M)
    (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (cursor : BinarySharedResourceRun.Cursor capacity hC) (pos localPos : ℕ)
    (hp : pos ≤ N) (hlp : localPos ≤ M) (hPos : pos = base + localPos) :
    BinarySharedResourceRun.runIndexed N bits cursor pos hp =
      WordStateMachine.offsetConsumed base (BinarySharedResourceRun.runIndexed M localBits cursor localPos hlp) := by
  cases cursor with
  | ready state =>
      conv_lhs => unfold BinarySharedResourceRun.runIndexed
      conv_rhs => unfold BinarySharedResourceRun.runIndexed
      cases hs : BinaryResourceChoice.prepare capacity hC state with
      | done result => simp only [WordStateMachine.offsetConsumed,hPos]
      | ask choice =>
          dsimp only
          exact runIndexed_offset N M base hSize bits localBits hBits
            (BinarySharedResourceRun.pending choice) pos localPos hp hlp hPos
  | coin choice a b hb hab =>
      conv_lhs => unfold BinarySharedResourceRun.runIndexed
      conv_rhs => unfold BinarySharedResourceRun.runIndexed
      dsimp only
      by_cases hz : a.isZero = true
      · simp only [hz,dite_true]
        exact runIndexed_offset N M base hSize bits localBits hBits
          (.ready (choice.select false)) pos localPos hp hlp hPos
      · simp only [hz,Bool.false_eq_true,dite_false]
        by_cases he : a.same b = true
        · simp only [he,dite_true]
          exact runIndexed_offset N M base hSize bits localBits hBits
            (.ready (choice.select true)) pos localPos hp hlp hPos
        · simp only [he,Bool.false_eq_true,dite_false]
          by_cases hRead : pos < N
          · have hLocal : localPos < M := by omega
            have hBit : bits ⟨pos,hRead⟩ = localBits ⟨localPos,hLocal⟩ := by
              simpa only [hPos] using (hBits ⟨localPos,hLocal⟩).symm
            simp only [dite_eq_left hRead,dite_eq_left hLocal,hBit]
            by_cases hd : localBits ⟨localPos,hLocal⟩ = (a.coinStep b).1
            · simp only [hd,ite_true]
              exact runIndexed_offset N M base hSize bits localBits hBits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b (by
                  have hn : a.value ≠ b.value := fun h => he ((a.same_value b).mpr h)
                  omega)).le) (pos + 1) (localPos + 1) (by omega) (by omega) (by omega)
            · simp only [hd,ite_false]
              exact runIndexed_offset N M base hSize bits localBits hBits
                (.ready (choice.select (!localBits ⟨localPos,hLocal⟩)))
                (pos + 1) (localPos + 1) (by omega) (by omega) (by omega)
          · have hLocal : ¬ localPos < M := by omega
            simp only [dite_eq_right hRead,dite_eq_right hLocal,WordStateMachine.offsetConsumed]
            simp only [hPos]
termination_by (N - pos,cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hw := prepared_state state choice hs
    simp only [BinarySharedResourceRun.pending,BinarySharedResourceRun.Cursor.rank]
    rw [hw]
    omega
  · apply Prod.Lex.right
    exact BinarySharedResourceRun.selected_rank_lt choice a b hb hab false
  · apply Prod.Lex.right
    exact BinarySharedResourceRun.selected_rank_lt choice a b hb hab true
  all_goals apply Prod.Lex.left
  all_goals omega

theorem runIndexed_window (N : ℕ) (bits : Fin N → Bool)
    (cursor : BinarySharedResourceRun.Cursor capacity hC) (pos : ℕ) (hp : pos ≤ N) :
    BinarySharedResourceRun.runIndexed N bits cursor pos hp =
      WordStateMachine.offsetConsumed pos
        (BinarySharedResourceRun.runIndexed (N - pos)
          (WordStateMachine.inputWindow bits pos (N - pos) (by omega)) cursor 0 (Nat.zero_le _)) := by
  apply runIndexed_offset N (N - pos) pos (by omega) bits _
  · intro index
    rfl
  · omega


end Blotto.BinaryPRGWordControllerThreeResourceReference
