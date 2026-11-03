import Blotto.GeneralPaperMatrixFieldCursor

/-! One directory installation writes every actual header and scalar cell.
Actual measured layout order derives all key uniqueness, roots and capacities.
This is the paper indexed RAM primitive model, not host allocator/GC cost. -/
namespace Blotto.GeneralPaperFieldDirectoryInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperRetainedScalarValue
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Installed (A : ℕ) where
  references : GeneralPaperPayloadMemory.Memory Word
  payloads : GeneralPaperPayloadMemory.Memory Scalar
  root : FixedBinaryWord A
  work : ℕ

def install (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : Installed A :=
  let references := GeneralPaperMixedReferenceRegionProgram.prepare model S A A [] directory.headers (GeneralPaperPayloadMemory.empty Word)
  let payloads := GeneralPaperPayloadMemory.install S A encode (GeneralPaperPayloadMemory.empty Scalar) (directory.cells.map Cell.entry)
  ⟨references.memory,payloads.1,directory.root.reference,references.work + payloads.2 + 128 * (S + A + 1)⟩

theorem scalar_keys (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ((directory.cells.map Cell.entry).map (fun entry => entry.1.value)).Nodup := by
  have hKeys := GeneralPaperMeasuredLayoutDistinct.reference_values model S A start plan hPos hCap
  have hSub := hSafe.2.2.1.map (fun region : Region A => region.reference.value)
  have h := hSub.nodup hKeys
  simpa only [List.map_map,Cell.entry,Function.comp_def] using h

theorem header_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (header : Header A) (hHeader : header ∈ directory.headers) (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model A (install model S A directory).references
      header.region.reference header.fixed j.val).1 = some (⟨A,header.targets[j.val]⟩ : Word) := by
  have hFrom : GeneralPaperReferenceLayoutInstallation.FromLayout model S A start plan directory.headers := hSafe.2.1
  exact GeneralPaperMixedReferenceRegionProgram.outside_read model S A A [] directory.headers
    (GeneralPaperPayloadMemory.empty Word) hA hSafe.2.2.2.1
    (GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.roots model S A start plan directory.headers hFrom hCap)
    (GeneralPaperReferenceLayoutInstallation.owners model S A start plan directory.headers hFrom) header hHeader j

theorem scalar_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hCap : start + plan.sizes.sum < 2 ^ A)
    (cell : Cell A) (hCell : cell ∈ directory.cells) :
    (GeneralPaperPayloadMemory.read A encode (install model S A directory).payloads cell.region.reference).1 = some cell.value ∧
      (GeneralPaperPayloadMemory.read A encode (install model S A directory).payloads cell.region.reference).2 = encode cell.value + 64 * A + 64 := by
  exact GeneralPaperPayloadMemory.read_installed S A encode (GeneralPaperPayloadMemory.empty Scalar) (directory.cells.map Cell.entry)
    (scalar_keys model S A start plan directory hSafe hPos hCap) cell.entry (List.mem_map.mpr ⟨cell,hCell,rfl⟩)

theorem root_value (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCap : start + plan.sizes.sum < 2 ^ A) :
    (install model S A directory).root.value = directory.root.start :=
  GeneralPaperMeasuredBlockLayout.references model S A start plan hCap directory.root hSafe.1

theorem scalar_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    (directory.cells.map (fun cell => encode cell.value)).sum ≤ plan.sizes.sum := by
  have hSub := hSafe.2.2.1.map Region.length
  have h := GeneralPaperReferenceHeaderSlotArea.sum_sublist _ _ hSub
  rw [GeneralPaperMeasuredBlockLayout.lengths] at h
  simp only [List.map_map,Function.comp_def] at h
  have hEq : directory.cells.map (fun cell => encode cell.value) = directory.cells.map (fun cell => cell.region.length) :=
    List.map_congr_left (fun cell hc => (hSafe.2.2.2.2 cell hc).symm)
  rw [hEq]
  exact h

theorem reference_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    A * GeneralPaperReferenceHeaderSlotArea.slots directory.headers ≤ plan.sizes.sum :=
  GeneralPaperReferenceHeaderSlotArea.layout_area model S A start plan directory.headers hSafe.2.1 hSafe.2.2.2.1

end Blotto.GeneralPaperFieldDirectoryInstallation
