import Blotto.RealPairProgram

/-! Real-RAM register/control cells for the actual append-only primitive runner.
The observer conservatively retains every prefix array and both arrays at a
push. Named real arithmetic uses one result cell; physical allocation/GC and
the whole PRG controller remain separate. -/

namespace Blotto.RealArithmeticProgram

noncomputable def retainedCells : List RealArithmeticInstruction → Array ℝ → ℕ
  | [], registers => registers.size
  | instruction :: rest, registers => registers.size + retainedCells rest (instruction.execute registers)

noncomputable def pushPeak : List RealArithmeticInstruction → Array ℝ → ℕ
  | [], registers => registers.size
  | instruction :: rest, registers =>
      max (registers.size + (instruction.execute registers).size)
        (pushPeak rest (instruction.execute registers))

theorem retainedCells_bound (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    retainedCells program registers ≤ (program.length + 1) * (registers.size + program.length) := by
  induction program generalizing registers with
  | nil => simp [retainedCells]
  | cons instruction rest ih =>
    have he := ih (instruction.execute registers)
    rw [instruction.execute_size] at he
    simp only [retainedCells, List.length_cons]
    nlinarith

theorem pushPeak_bound (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    pushPeak program registers ≤ 2 * (registers.size + program.length) := by
  induction program generalizing registers with
  | nil => simp [pushPeak]; omega
  | cons instruction rest ih =>
    have he := ih (instruction.execute registers)
    rw [instruction.execute_size] at he
    simp only [pushPeak, instruction.execute_size, List.length_cons]
    apply max_le <;> omega

noncomputable def storageAllowance (program : List RealArithmeticInstruction) (registers : Array ℝ) : ℕ :=
  retainedCells program registers + pushPeak program registers + 4 * (program.length + 1)

theorem storageAllowance_bound (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    storageAllowance program registers ≤ (program.length + 3) * (registers.size + program.length) + 4 * (program.length + 1) := by
  have hr := retainedCells_bound program registers
  have hp := pushPeak_bound program registers
  unfold storageAllowance
  nlinarith

noncomputable def runWithStorage : List RealArithmeticInstruction → Array ℝ → Array ℝ × ℕ
  | [], registers => (registers, registers.size + 4)
  | instruction :: rest, registers =>
      let next := instruction.execute registers
      let later := runWithStorage rest next
      (later.1, registers.size + later.2 + 4)

theorem runWithStorage_state (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    (runWithStorage program registers).1 = run program registers := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.execute registers)

theorem runWithStorage_retained (program : List RealArithmeticInstruction) (registers : Array ℝ) :
    (runWithStorage program registers).2 = retainedCells program registers + 4 * (program.length + 1) := by
  induction program generalizing registers with
  | nil => simp [runWithStorage, retainedCells]
  | cons instruction rest ih =>
    simp only [runWithStorage, retainedCells, ih, List.length_cons]
    ring

end Blotto.RealArithmeticProgram

namespace Blotto.RealPairProgram

theorem storageAllowance_pair (pair : RoundingPair) :
    RealArithmeticProgram.storageAllowance code (inputs pair) ≤ 152 := by
  have he := RealArithmeticProgram.storageAllowance_bound code (inputs pair)
  have hs : (inputs pair).size = 5 := rfl
  rw [hs, operations] at he
  exact he

theorem real_pair_retained_storage (pair : RoundingPair) :
    (RealArithmeticProgram.runWithStorage code (inputs pair)).1 = run pair ∧
      (RealArithmeticProgram.runWithStorage code (inputs pair)).2 ≤ 128 := by
  refine ⟨RealArithmeticProgram.runWithStorage_state _ _, ?_⟩
  rw [RealArithmeticProgram.runWithStorage_retained]
  have he := RealArithmeticProgram.retainedCells_bound code (inputs pair)
  have hs : (inputs pair).size = 5 := rfl
  rw [hs, operations] at he
  rw [operations]
  omega

end Blotto.RealPairProgram
