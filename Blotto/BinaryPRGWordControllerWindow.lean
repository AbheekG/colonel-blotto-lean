import Blotto.BinaryCategoricalRun
import Blotto.BinaryStoredCoinIndexed
import Blotto.WordMachineRunEmbedding

/-! Proof-only fixed-window offset simulation for the retained categorical
continuation. Runtime Boolean-PC controllers keep the whole seed Store/cap;
inputWindow and numerical offsets appear solely in their legacy refinement. -/

namespace Blotto.BinaryPRGWordControllerWindow

theorem inputWindow_nested (N base M localPos count : ℕ) (bits : Fin N → Bool)
    (hOuter : base + M ≤ N) (hInner : localPos + count ≤ M)
    (hGlobal : (base + localPos) + count ≤ N) :
    WordStateMachine.inputWindow (WordStateMachine.inputWindow bits base M hOuter) localPos count hInner =
      WordStateMachine.inputWindow bits (base + localPos) count hGlobal := by
  funext index
  unfold WordStateMachine.inputWindow
  congr 1
  apply Fin.ext
  simp only
  omega

theorem coinRun_offset {width : ℕ} (N M base : ℕ) (hSize : N = base + M)
    (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (a b : FixedBinaryWord width) (pos localPos : ℕ) (hp : pos ≤ N) (hlp : localPos ≤ M)
    (hPos : pos = base + localPos) :
    BinaryStoredCoinIndexed.run N bits a b pos hp =
      WordStateMachine.offsetConsumed base (BinaryStoredCoinIndexed.run M localBits a b localPos hlp) := by
  conv_lhs => unfold BinaryStoredCoinIndexed.run
  conv_rhs => unfold BinaryStoredCoinIndexed.run
  by_cases hz : a.isZero = true
  · simp only [hz,ite_true,WordStateMachine.offsetConsumed,hPos]
  · simp only [hz,Bool.false_eq_true,ite_false]
    by_cases he : a.same b = true
    · simp only [he,ite_true,WordStateMachine.offsetConsumed,hPos]
    · simp only [he,Bool.false_eq_true,ite_false]
      by_cases hr : pos < N
      · have hlr : localPos < M := by omega
        have hBit : bits ⟨pos,hr⟩ = localBits ⟨localPos,hlr⟩ := by
          simpa only [hPos] using (hBits ⟨localPos,hlr⟩).symm
        simp only [dite_eq_left hr,dite_eq_left hlr,hBit]
        split
        · exact coinRun_offset N M base hSize bits localBits hBits (a.coinStep b).2 b
            (pos + 1) (localPos + 1) (by omega) (by omega) (by omega)
        · simp only [WordStateMachine.offsetConsumed]
          congr 1
          omega
      · have hlr : ¬ localPos < M := by omega
        simp only [dite_eq_right hr,dite_eq_right hlr,WordStateMachine.offsetConsumed]
        exact congrArg (fun p => (none,p)) hPos
termination_by N - pos

theorem coinSample_offset (N M base : ℕ) (hSize : N = base + M)
    (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (word : BinaryRationalNormalization.SignedWord) (pos localPos : ℕ)
    (hp : pos ≤ N) (hlp : localPos ≤ M) (hPos : pos = base + localPos) :
    BinaryStoredCoinIndexed.sample word N bits pos hp =
      WordStateMachine.offsetConsumed base (BinaryStoredCoinIndexed.sample word M localBits localPos hlp) :=
  coinRun_offset N M base hSize bits localBits hBits _ _ pos localPos hp hlp hPos

theorem runCursorIndexed_offset {S α : Type*} (machine : WordStateMachine S α)
    (N M base : ℕ) (hSize : N = base + M) (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (cursor : WordCursor S) (pos localPos : ℕ) (hp : pos ≤ N) (hlp : localPos ≤ M)
    (hPos : pos = base + localPos) :
    machine.runCursorIndexed N bits cursor pos hp =
      WordStateMachine.offsetConsumed base (machine.runCursorIndexed M localBits cursor localPos hlp) := by
  rw [machine.runCursorIndexed_window N bits cursor pos (M - localPos) (by omega),
    machine.runCursorIndexed_window M localBits cursor localPos (M - localPos) (by omega)]
  have hWindow : WordStateMachine.inputWindow bits pos (M - localPos) (by omega) =
      WordStateMachine.inputWindow localBits localPos (M - localPos) (by omega) := by
    funext index
    unfold WordStateMachine.inputWindow
    rw [hBits ⟨localPos + index.val,by omega⟩]
    congr 1
    apply Fin.ext
    dsimp only
    omega
  rw [hWindow]
  unfold WordStateMachine.offsetConsumed
  congr 1
  omega

theorem categorical_offset {α : Type*} (fallback : α) (N M base : ℕ) (hSize : N = base + M)
    (bits : Fin N → Bool) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index = bits ⟨base + index.val,by rw [hSize]; omega⟩)
    (cursor : BinaryCategoricalRun.Cursor α) (pos localPos : ℕ) (hp : pos ≤ N) (hlp : localPos ≤ M)
    (hPos : pos = base + localPos) :
    BinaryCategoricalRun.runIndexed fallback N bits cursor pos hp =
      WordStateMachine.offsetConsumed base (BinaryCategoricalRun.runIndexed fallback M localBits cursor localPos hlp) := by
  rw [BinaryCategoricalRun.runIndexed_refines,BinaryCategoricalRun.runIndexed_refines]
  exact runCursorIndexed_offset (categoricalMachine fallback) N M base hSize bits localBits hBits
    cursor.reference pos localPos hp hlp hPos

end Blotto.BinaryPRGWordControllerWindow
