import Blotto.GeneralPaperCellInstructionPrice

/-! A final nonnegative batch effect bounds its first instruction and the
remaining batch after that instruction. Every intermediate cache/state cap
is derived from the same code-level invariant; no validation pass executes.
-/
namespace Blotto.GeneralPaperBatchUpdateState
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalBatch
open GeneralPaperPreparedPowers GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem head_state (lambda k height : ℕ) (span : ℚ) (n : Node height) (entry : Instruction) (rest : List Instruction)
    (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+effect (entry::rest) i≤GeneralPaperPowerPrecision.levelBound lambda k) :
    let updated := GeneralPaperIntervalUpdate.run (prepare lambda k) entry.lo entry.hi entry.amount height n 0 span
    (∀ i<2^height,levelAt n i+increment entry i≤GeneralPaperPowerPrecision.levelBound lambda k) ∧
    Valid lambda k updated.node ∧
    (∀ i<2^height,levelAt updated.node i+effect rest i≤GeneralPaperPowerPrecision.levelBound lambda k) := by
  have hHead : ∀ i<2^height,levelAt n i+increment entry i≤GeneralPaperPowerPrecision.levelBound lambda k := by
    intro i hi
    have h := hFinal i hi
    dsimp only [effect] at h
    omega
  refine ⟨hHead,?_,?_⟩
  · apply GeneralPaperIntervalOutputValidity.run_valid_of_output lambda k entry.lo entry.hi entry.amount height n 0 span hValid
    intro i hi
    rw [step_levels _ height span n entry hSpan i hi]
    exact hHead i hi
  · intro i hi
    rw [step_levels _ height span n entry hSpan i hi]
    have h := hFinal i hi
    dsimp only [effect] at h
    omega

theorem prefix_paths (lambda k height : ℕ) (span : ℚ) (n : Node height) (entries : List Instruction)
    (hSpan : span=(2:ℚ)^height)
    (hFinal : ∀ i<2^height,levelAt n i+effect entries i≤GeneralPaperPowerPrecision.levelBound lambda k) (count : ℕ) :
    PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalBatch.run (prepare lambda k) height span n (entries.take count)).node := by
  intro i hi
  rw [Nat.zero_add,run_levels _ height span n (entries.take count) hSpan i hi]
  have hp := GeneralPaperIntervalBatchBounds.effect_take_le entries count i
  have hf := hFinal i hi
  omega

end Blotto.GeneralPaperBatchUpdateState
