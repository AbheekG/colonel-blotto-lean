import Blotto.GeneralPaperReferenceCollectionLifetime

/-! Complete reference collection at actual measured directories. The
full position-bearing source list coexists with the installer projection
and resident memory. Work majorants are proved from the executed source,
and are used only to bound saved scalar widths. -/
namespace Blotto.GeneralPaperDirectoryReferenceCollectionLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperFieldDirectoryPartition (Covered)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperUnifiedFieldValue (Memory encode)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def window (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : ℕ :=
  GeneralPaperReferenceCollectionLifetime.window model S A directory.headers

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (2 * B + 1) * GeneralPaperReferenceCollectionLifetime.unit model S A
    (GeneralPaperStoredDirectoryPreparationWork.installBound model S A B)

theorem work_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).work ≤
      GeneralPaperStoredDirectoryPreparationWork.installBound model S A plan.sizes.sum := by
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hWork := GeneralPaperStoredReferencePreparationWork.collect_work model S A directory.headers hA hSafe.2.2.2.1 hCaps
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have h0 := Nat.mul_le_mul_right (GeneralPaperStoredReferencePreparationWork.perElement model S A) hSlots
  have h1 := Nat.mul_le_mul_right (192 * (S + A + 1)) hCounts.1
  unfold GeneralPaperStoredDirectoryPreparationWork.installBound
  omega

theorem window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A directory ≤ profile model S A plan.sizes.sum := by
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hWork := work_bound model S A start plan directory hSafe hPos hA hCap
  have hWindow := GeneralPaperReferenceCollectionLifetime.window_bound model S A _ directory.headers hA hSafe.2.2.2.1 hCaps hWork
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  exact hWindow.trans (Nat.mul_le_mul_right _ (by omega))

theorem count_expanded_window (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A (GeneralPaperHeaderCountDirectory.prepare model S A directory).1 ≤ profile model S A plan.sizes.sum := by
  rw [GeneralPaperHeaderCountDirectory.data]
  exact window_bound model S A start plan _ (GeneralPaperHeaderCountDirectory.safe _ directory hSafe) hPos hA hCap

theorem collected_position_owner (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    GeneralPaperEncodedScalarStorage.listFootprint S (GeneralPaperReferenceSlotLifetime.entryFoot S)
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries ≤ profile model S A plan.sizes.sum := by
  have h := window_bound model S A start plan directory hSafe hPos hA hCap
  unfold window GeneralPaperReferenceCollectionLifetime.window at h
  omega

theorem caller_full_view_coexistence (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hMemory : Bounded encode memory B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∃ keys : Finset ℕ,(∀ key,(GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key) +
        GeneralPaperDirectoryInstallationLifetime.window model S A directory memory + window model S A directory ≤
      B + plan.sizes.sum + GeneralPaperDirectoryInstallationLifetime.profile model S A plan.sizes.sum +
        profile model S A plan.sizes.sum := by
  obtain ⟨keys,hSupport,hInstall⟩ := GeneralPaperDirectoryInstallationLifetime.resident_coexistence
    model S A start B plan directory memory hMemory hSafe hCovered hPos hA hCap
  exact ⟨keys,hSupport,Nat.add_le_add hInstall (window_bound model S A start plan directory hSafe hPos hA hCap)⟩

end Blotto.GeneralPaperDirectoryReferenceCollectionLifetime
