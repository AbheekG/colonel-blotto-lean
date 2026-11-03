import Blotto.GeneralPaperScalarFieldCursorLifetime

/-! Actual scalar-cell to reference-target traversal. Complete pending
cell records, saved prices and the single returned word list are counted.
Cell scalar payloads retain one additive sum, including original budgets. -/
namespace Blotto.GeneralPaperScalarCursorTargetLifetime
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperScalarArrayFieldCursor (targets)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def frames (S A : ℕ) (cells : List (Cell A)) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.liftFrames S A (GeneralPaperFieldDirectoryStorage.cellFoot S)
    (fun values => (targets S A values).2) cells

def window (S A : ℕ) (cells : List (Cell A)) : ℕ :=
  listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) cells + frames S A cells +
    listFootprint S (fun _ : FixedBinaryWord A => A) (targets S A cells).1 +
    fields S [S,A,(targets S A cells).2] + 64 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (cells : List (Cell A)) (hA : 0 < A)
    (hCap : ∀ cell ∈ cells,cell.region.stop < 2 ^ A) (hWork : (targets S A cells).2 ≤ Q) :
    window S A cells ≤ 2 * (cells.map (fun cell => encode cell.value)).sum + (cells.length + 1) * 4 * unit model S A Q := by
  have hCells := GeneralPaperFieldDirectoryStorage.cells_bound S A cells (fun cell hc =>
    GeneralPaperMeasuredLayoutStorage.region_bound S A cell.region hA (hCap cell hc))
  have hFrames := GeneralPaperUnifiedInstallationLifetime.lift_frames_bound S A Q (GeneralPaperFieldDirectoryStorage.cellFoot S)
    (fun values => (targets S A values).2) cells (fun _ _ => by dsimp only [targets]; omega) hWork
  have hTargets := list_bound S A (fun _ : FixedBinaryWord A => A) (targets S A cells).1 (fun _ _ => le_rfl)
  rw [GeneralPaperScalarArrayFieldCursor.targets_data,List.length_map] at hTargets
  have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(targets S A cells).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hStep : 384 * (S + A + 1) + 4 * S + A + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A Q ≤ unit model S A Q := by
    unfold GeneralPaperUnifiedInstallationLifetime.liftFrameBound
    omega
  have hPay := Nat.mul_le_mul_left (cells.length + 1) hStep
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ cells.length + 1 by omega)
  unfold window frames
  rw [GeneralPaperScalarArrayFieldCursor.targets_data]
  change ((cells.map (GeneralPaperFieldDirectoryStorage.cellFoot S)).sum + cells.length * (2 * S) + 32 * S) + _ + _ + _ + 64 * S ≤ _
  nlinarith only [hCells,hFrames,hTargets,hFields,hPay,hBase,hUnit]

theorem exact_targets (S A : ℕ) (cells : List (Cell A)) :
    (targets S A cells).1 = cells.map (fun cell => cell.region.reference) :=
  GeneralPaperScalarArrayFieldCursor.targets_data S A cells

end Blotto.GeneralPaperScalarCursorTargetLifetime
