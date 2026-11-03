import Blotto.AdaptiveKernelHistory

/-! A concrete flat fair-bit execution supplies one fresh fixed-width block
per adaptive round. The complete history kernel is derived from the actual
runner. A uniform per-round bit cap is explicit and must be supplied by the
algorithm's global resource bound; this module does not invent that cap. -/

namespace Blotto
open scoped Classical

noncomputable def bitHistoryStep {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (history : List α) : BoundedExpectationKernel α :=
  (fairBitKernel B).map (sample history)

def runBitHistory {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α) :
    (T : ℕ) → (Fin (T * B) → Bool) → List α → List α
  | 0, _bits, history => history
  | T + 1, bits, history =>
      let flat : Fin (B + T * B) → Bool := fun j => bits (j.cast (by ring))
      let observed := sample history (firstBitBlock B (T * B) flat)
      runBitHistory B sample T (secondBitBlock B (T * B) flat) (observed :: history)

theorem runBitHistory_length {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (T : ℕ) (bits : Fin (T * B) → Bool) (history : List α) :
    (runBitHistory B sample T bits history).length = T + history.length := by
  induction T generalizing history with
  | zero => simp [runBitHistory]
  | succ T ih =>
    rw [runBitHistory, ih]
    simp only [List.length_cons]
    omega

theorem runBitHistory_mean {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (T : ℕ) (history : List α) (test : List α → ℝ) :
    (fairBitKernel (T * B)).mean (fun bits => test (runBitHistory B sample T bits history)) =
      (BoundedExpectationKernel.historyRun (bitHistoryStep B sample) T history).mean test := by
  induction T generalizing history with
  | zero =>
    simp only [runBitHistory]
    rw [BoundedExpectationKernel.historyRun]
    exact (fairBitKernel (0 * B)).constant (test history)
  | succ T ih =>
    have hWidth : (T + 1) * B = B + T * B := by ring
    unfold runBitHistory
    rw [fairBitKernel_cast ((T + 1) * B) (B + T * B) hWidth
      (fun flat => test (runBitHistory B sample T (secondBitBlock B (T * B) flat)
        (sample history (firstBitBlock B (T * B) flat) :: history)))]
    rw [fairBitKernel_blocks B (T * B) (fun first second =>
      test (runBitHistory B sample T second (sample history first :: history)))]
    simp_rw [ih]
    rfl

theorem runBitHistory_event_error {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (ideal : List α → BoundedExpectationKernel α) (error : ℝ) (herror : 0 ≤ error)
    (hStep : ∀ history, (bitHistoryStep B sample history).Close (ideal history) error)
    (T : ℕ) (history : List α) (event : Set (List α)) :
    |(fairBitKernel (T * B)).mean (fun bits => if runBitHistory B sample T bits history ∈ event then 1 else 0) -
      (BoundedExpectationKernel.historyRun ideal T history).mean (fun h => if h ∈ event then 1 else 0)| ≤ (T : ℝ) * error := by
  rw [runBitHistory_mean B sample T history (fun h => if h ∈ event then 1 else 0)]
  exact BoundedExpectationKernel.historyRun_event_error (bitHistoryStep B sample) ideal error herror hStep T history event

theorem runBitHistory_bounded_error {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (ideal : List α → BoundedExpectationKernel α) (error : ℝ) (herror : 0 ≤ error)
    (hStep : ∀ history, (bitHistoryStep B sample history).Close (ideal history) error)
    (T : ℕ) (history : List α) (test : List α → ℝ) (hTest : ∀ h, 0 ≤ test h ∧ test h ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (runBitHistory B sample T bits history)) -
      (BoundedExpectationKernel.historyRun ideal T history).mean test| ≤ (T : ℝ) * error := by
  rw [runBitHistory_mean B sample T history test]
  exact BoundedExpectationKernel.historyRun_close (bitHistoryStep B sample) ideal error herror hStep T history test hTest

theorem runBitHistory_bounded_error_before {α : Type*} (B : ℕ) (sample : List α → (Fin B → Bool) → α)
    (ideal : List α → BoundedExpectationKernel α) (error : ℝ) (herror : 0 ≤ error) (limit : ℕ)
    (hStep : ∀ history, history.length < limit → (bitHistoryStep B sample history).Close (ideal history) error)
    (T : ℕ) (history : List α) (hLength : T + history.length ≤ limit)
    (test : List α → ℝ) (hTest : ∀ h, 0 ≤ test h ∧ test h ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (runBitHistory B sample T bits history)) -
      (BoundedExpectationKernel.historyRun ideal T history).mean test| ≤ (T : ℝ) * error := by
  rw [runBitHistory_mean B sample T history test]
  exact BoundedExpectationKernel.historyRun_close_before (bitHistoryStep B sample) ideal error herror limit hStep T history hLength test hTest

end Blotto
