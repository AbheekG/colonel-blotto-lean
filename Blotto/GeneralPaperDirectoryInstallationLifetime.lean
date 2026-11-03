import Blotto.GeneralPaperUnifiedInstallationLifetime

/-! Instantiate the complete unified installer lifetime at actual safe
directories. Measured ownership derives entry counts, additive payload
area and the full preparation price. No component price premise remains.
The same result includes incoming/final resident RAM and count-expanded
input directories; enclosing cursor/count/collection frames remain separate. -/
namespace Blotto.GeneralPaperDirectoryInstallationLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperFieldDirectoryPartition (Covered)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperPayloadMemoryOwnership (Bounded payload cellSize)
open GeneralPaperUnifiedFieldValue (Memory encode)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def window (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.window S A
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.profile S A B B B (GeneralPaperStoredDirectoryPreparationWork.installBound model S A B)

theorem entry_parameters (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) :
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.length ≤ plan.sizes.sum ∧
      (directory.cells.map Cell.entry).length ≤ plan.sizes.sum ∧
      payload GeneralPaperRetainedScalarValue.encode (directory.cells.map Cell.entry) ≤ plan.sizes.sum ∧
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.length * A +
        payload GeneralPaperRetainedScalarValue.encode (directory.cells.map Cell.entry) ≤ plan.sizes.sum := by
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hArea := GeneralPaperDirectoryCopyWork.payload_area model S A start plan directory hSafe
  have hJoint := GeneralPaperFieldDirectorySeparation.joint_area model S A start plan directory hSafe hCovered
  simp only [GeneralPaperReferenceRegionProgram.count,GeneralPaperReferenceHeaderSlotArea.slots,
    payload,List.map_map,Cell.entry,Function.comp_def,List.length_map] at hSlots hJoint ⊢
  exact ⟨hSlots,hCounts.2,hArea,by nlinarith only [hJoint]⟩

theorem prepare_price (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (GeneralPaperUnifiedFieldMemory.prepare S A
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory).2 ≤
        GeneralPaperStoredDirectoryPreparationWork.installBound model S A plan.sizes.sum := by
  have h := GeneralPaperStoredDirectoryPreparationWork.extension_work model S A start plan directory memory hSafe hCovered hPos hA hCap
  change (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).work +
    (GeneralPaperUnifiedFieldMemory.prepare S A
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory).2 +
    128 * (S + A + 1) ≤ _ at h
  omega

theorem window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A directory memory ≤ profile model S A plan.sizes.sum := by
  have hWork := prepare_price model S A start plan directory memory hSafe hCovered hPos hA hCap
  have hParameters := entry_parameters model S A start plan directory hSafe hCovered hPos hA
  have hWindow := GeneralPaperUnifiedInstallationLifetime.window_bound S A _
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory hWork
  exact hWindow.trans (GeneralPaperUnifiedInstallationLifetime.profile_mono S A _ _ _ _ _ _ _
    hParameters.1 hParameters.2.1 hParameters.2.2.1)

theorem resident_coexistence (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hMemory : Bounded encode memory B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∃ keys : Finset ℕ,(∀ key,(GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key) +
        window model S A directory memory ≤ B + plan.sizes.sum + profile model S A plan.sizes.sum := by
  have hWork := prepare_price model S A start plan directory memory hSafe hCovered hPos hA hCap
  have hParameters := entry_parameters model S A start plan directory hSafe hCovered hPos hA
  obtain ⟨keys,hSupport,hCoexistence⟩ := GeneralPaperUnifiedInstallationLifetime.resident_coexistence S A B _
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory hMemory hWork
  have hMajor := GeneralPaperUnifiedInstallationLifetime.profile_mono S A _ _ _ _ _ _
    (GeneralPaperStoredDirectoryPreparationWork.installBound model S A plan.sizes.sum)
    hParameters.1 hParameters.2.1 hParameters.2.2.1
  refine ⟨keys,hSupport,?_⟩
  dsimp only [window,profile,GeneralPaperStoredDirectoryExtension.install]
  omega

theorem count_expanded_window (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A (GeneralPaperHeaderCountDirectory.prepare model S A directory).1 memory ≤ profile model S A plan.sizes.sum := by
  rw [GeneralPaperHeaderCountDirectory.data]
  exact window_bound model S A start plan _ memory (GeneralPaperHeaderCountDirectory.safe _ directory hSafe)
    (GeneralPaperHeaderCountDirectory.covered _ directory hCovered) hPos hA hCap

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (B x)) r L := by
  have hAllWork := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hB
  have hInstallWork : Bound (fun x => GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (B x)) r L := by
    apply dominated hAllWork
    intro x
    unfold GeneralPaperStoredDirectoryPreparationWork.bound
    omega
  have hQ := bound_small hL hInstallWork hrSmall
  exact GeneralPaperUnifiedInstallationLifetime.profile_rate S A B B B
    (fun x => GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (B x)) r L
    hL hr hS hA hB hB hB hQ

end Blotto.GeneralPaperDirectoryInstallationLifetime
