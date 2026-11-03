import Blotto.GeneralPaperStoredReferencePreparationWork

/-! Complete count initialization and unified-memory installation are
linear in the actual measured extent, up to address-only factors. One
payload sum pays for every scalar copy; no largest scalar is charged per
field. The final theorem prices the constructor actually used by readers. -/
namespace Blotto.GeneralPaperStoredDirectoryPreparationWork
open GeneralPaperFieldDirectory GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperReferenceRegionSlots GeneralPaperSequentialLayout
open GeneralPaperMeasuredBlockPlan (Plan)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def countBound (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (2 * B + 1) * GeneralPaperStoredHeaderPreparationWork.perElement model S A +
    (B + 2) * (64 * (S + A + 1)) + 4 * A + 2 + 64 * (S + A + 1)

def installBound (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  B * GeneralPaperStoredReferencePreparationWork.perElement model S A +
    B * (192 * (S + A + 1)) + 64 * (S + A + 1) +
    B * (67 * A + 64 + 128 * (S + A + 1)) + 2 * B +
    B * (65 * A + 64 + 128 * (S + A + 1)) + 512 * (S + A + 1)

def bound (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  countBound model S A B + installBound model S A B + 128 * (S + A + 1)

theorem directory_counts (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) :
    directory.headers.length ≤ plan.sizes.sum ∧ directory.cells.length ≤ plan.sizes.sum := by
  have hh := hSafe.2.1.length_le
  have hc := hSafe.2.2.1.length_le
  rw [List.length_map,GeneralPaperMeasuredBlockLayout.count] at hh hc
  have hp := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  omega

theorem count_work (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperHeaderCountDirectory.prepare model S A directory).2 ≤ countBound model S A plan.sizes.sum := by
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hHeaders := GeneralPaperStoredHeaderPreparationWork.headers_work model S A directory.headers hA hSafe.2.2.2.1 hCaps
  have hExpanded := GeneralPaperHeaderCountDirectory.safe _ directory hSafe
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan
    (GeneralPaperHeaderCountDirectory.expanded directory).headers hExpanded.2.1 hA hExpanded.2.2.2.1
  have hCounts := directory_counts model S A start plan directory hSafe hPos
  have hRoot := GeneralPaperLastRegionSelection.layout_price model S A start plan hA hCap directory.root hSafe.1
  have hSum : (directory.headers.map (fun h => (GeneralPaperHeaderCountExpansion.run model S A h).2)).sum ≤
      (2 * plan.sizes.sum + 1) * GeneralPaperStoredHeaderPreparationWork.perElement model S A :=
    hHeaders.trans (Nat.mul_le_mul_right _ (by change _ ≤ _ at hSlots; dsimp only [GeneralPaperHeaderCountDirectory.expanded] at hSlots; omega))
  have hOverhead := Nat.mul_le_mul_right (64 * (S + A + 1)) (Nat.add_le_add_right hCounts.1 2)
  rw [GeneralPaperHeaderCountDirectory.work]
  unfold countBound
  omega

theorem install_work (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperUnifiedDirectoryInstallation.install model S A directory).work ≤ installBound model S A plan.sizes.sum := by
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hCollect := GeneralPaperStoredReferencePreparationWork.collect_work model S A directory.headers hA hSafe.2.2.2.1 hCaps
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hCounts := directory_counts model S A start plan directory hSafe hPos
  have hArea := GeneralPaperFieldDirectorySeparation.joint_area model S A start plan directory hSafe hCovered
  have hp : (directory.cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum ≤ plan.sizes.sum := by omega
  have h0 := Nat.mul_le_mul_right (GeneralPaperStoredReferencePreparationWork.perElement model S A) hSlots
  have h1 := Nat.mul_le_mul_right (192 * (S + A + 1)) hCounts.1
  have h2 := Nat.mul_le_mul_right (67 * A + 64 + 128 * (S + A + 1)) hSlots
  have h3 := Nat.mul_le_mul_right (65 * A + 64 + 128 * (S + A + 1)) hCounts.2
  rw [GeneralPaperUnifiedDirectoryInstallation.install_work]
  unfold installBound
  omega

theorem finish_work (model : RationalCostModel) (S A start prefixWork : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperHeaderCountInstallation.finish model S A prefixWork directory).work ≤
      prefixWork + bound model S A plan.sizes.sum := by
  have hCount := count_work model S A start plan directory hSafe hPos hA hCap
  have hInstall := install_work model S A start plan (GeneralPaperHeaderCountDirectory.expanded directory)
    (GeneralPaperHeaderCountDirectory.safe _ directory hSafe) (GeneralPaperHeaderCountDirectory.covered _ directory hCovered) hPos hA hCap
  rw [GeneralPaperHeaderCountInstallation.work]
  unfold bound
  omega

theorem extension_work_eq (model : RationalCostModel) (S A : ℕ) (directory : Directory A)
    (memory : GeneralPaperUnifiedFieldValue.Memory) :
    (GeneralPaperStoredDirectoryExtension.install model S A directory memory).work =
      (GeneralPaperUnifiedDirectoryInstallation.install model S A directory).work := by
  simp only [GeneralPaperStoredDirectoryExtension.install,GeneralPaperUnifiedDirectoryInstallation.install,
    GeneralPaperUnifiedFieldMemory.prepare_work]

theorem extension_work (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (memory : GeneralPaperUnifiedFieldValue.Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperStoredDirectoryExtension.install model S A directory memory).work ≤ installBound model S A plan.sizes.sum := by
  rw [extension_work_eq]
  exact install_work model S A start plan directory hSafe hCovered hPos hA hCap

end Blotto.GeneralPaperStoredDirectoryPreparationWork
