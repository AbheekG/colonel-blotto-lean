import Blotto.RealStateMachine

/-! The indexed real-RAM control path refines exact real-choice semantics
for every seed window, including the number of uniform inputs consumed. -/

namespace Blotto.RealStateMachine
open MeasureTheory

def seedWindow {N : ℕ} (seed : Fin N → ℝ) (pos length : ℕ) (h : pos + length ≤ N) : Fin length → ℝ :=
  fun j => seed ⟨pos + j.val, by omega⟩

theorem seedWindow_head {N : ℕ} (seed : Fin N → ℝ) (pos length : ℕ) (h : pos + (length + 1) ≤ N) :
    seedWindow seed pos (length + 1) h 0 = seed ⟨pos, by omega⟩ := by simp [seedWindow]

theorem seedWindow_tail {N : ℕ} (seed : Fin N → ℝ) (pos length : ℕ) (h : pos + (length + 1) ≤ N) :
    Fin.tail (seedWindow seed pos (length + 1) h) = seedWindow seed (pos + 1) length (by omega) := by
  funext j
  change seed ⟨pos + (j.val + 1), by omega⟩ = seed ⟨pos + 1 + j.val, by omega⟩
  congr 1
  apply Fin.ext
  change pos + (j.val + 1) = pos + 1 + j.val
  omega

theorem seedWindow_zero {N : ℕ} (seed : Fin N → ℝ) : seedWindow seed 0 N (by omega) = seed := by
  funext j
  simp [seedWindow]

theorem specification_done {S α : Type*} (m : RealStateMachine S α) (s : S) (x : α) (h : m.step s = .done x) :
    m.specification s = .leaf x := by unfold specification; rw [h]

theorem specification_ask {S α : Type*} (m : RealStateMachine S α) (s : S) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : S) (h : m.step s = .ask p hp upper lower) :
    m.specification s = .fork p hp (m.specification upper) (m.specification lower) := by
  conv_lhs => unfold specification
  rw [h]

theorem runIndexed_window {S α : Type*} (m : RealStateMachine S α) (N : ℕ) (seed : Fin N → ℝ)
    (s : S) (pos length : ℕ) (h : pos + length = N) :
    m.runIndexed N seed s pos (by omega) =
      (let result := (m.specification s).sample length (seedWindow seed pos length (by omega))
       (result.1, pos + result.2)) := by
  cases hs : m.step s with
  | done x =>
    conv_lhs => unfold runIndexed
    rw [hs, m.specification_done s x hs]
    cases length <;> simp [RealChoiceTree.sample]
  | ask p hp upper lower =>
    conv_lhs => unfold runIndexed
    rw [hs, m.specification_ask s p hp upper lower hs]
    dsimp only
    cases length with
    | zero =>
      have hRead : ¬pos < N := by omega
      simp [hRead, RealChoiceTree.sample]
    | succ length =>
      have hRead : pos < N := by omega
      rw [dite_eq_left hRead, RealChoiceTree.sample_fork_succ, seedWindow_head]
      dsimp only
      rw [seedWindow_tail]
      by_cases hChoice : seed ⟨pos, hRead⟩ ≤ p
      · simp only [hChoice, ite_true]
        have ih := m.runIndexed_window N seed upper (pos + 1) length (by omega)
        rw [ih]
        dsimp only
        congr 1
        omega
      · simp only [hChoice, ite_false]
        have ih := m.runIndexed_window N seed lower (pos + 1) length (by omega)
        rw [ih]
        dsimp only
        congr 1
        omega
termination_by length
decreasing_by all_goals omega

theorem run_refines {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (seed : Fin C → ℝ) :
    m.run C s seed = (m.specification s).sample C seed := by
  have h := m.runIndexed_window C seed s 0 C (by omega)
  simpa only [run, seedWindow_zero, Nat.zero_add, Prod.mk.eta] using h

theorem run_total {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (seed : Fin C → ℝ)
    (hC : m.rank s ≤ C) : (m.run C s seed).1 ≠ none := by
  rw [m.run_refines]
  exact (m.specification s).sample_total C seed (m.specification_height s |>.trans hC)

theorem run_reads_rank {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (seed : Fin C → ℝ) :
    (m.run C s seed).2 ≤ m.rank s := by
  rw [m.run_refines]
  exact ((m.specification s).sample_reads_height C seed).trans (m.specification_height s)

theorem output_refines {S α : Type*} (m : RealStateMachine S α) (C : ℕ) (s : S) (fallback : α) (seed : Fin C → ℝ) :
    m.output C s fallback seed = (m.specification s).output C fallback seed := by
  unfold output RealChoiceTree.output
  rw [m.run_refines]

theorem output_law {S α : Type*} [MeasurableSpace α] (m : RealStateMachine S α) (C : ℕ) (s : S)
    (fallback : α) (hC : m.rank s ≤ C) :
    Measure.map (m.output C s fallback) (RealUniformInputs.law C : Measure (Fin C → ℝ)) =
      ((m.specification s).idealLaw : Measure α) := by
  have h : m.output C s fallback = (m.specification s).output C fallback := funext (m.output_refines C s fallback)
  rw [h]
  exact (m.specification s).output_law C fallback ((m.specification_height s).trans hC)

end Blotto.RealStateMachine
