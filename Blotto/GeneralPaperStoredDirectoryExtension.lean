import Blotto.GeneralPaperStoredNativeConstruction

/-! Directory installation extends an existing combined memory. Outer
headers/scalars use their own address width, while previously installed
inner cells remain in the same address map. -/
namespace Blotto.GeneralPaperStoredDirectoryExtension
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedFieldValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def install (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) : Installed A :=
  let words := GeneralPaperReferenceRegionProgram.collect model S A directory.headers
  let actual := GeneralPaperUnifiedFieldMemory.prepare S A words.entries (directory.cells.map Cell.entry) memory
  ⟨actual.1,directory.root.reference,words.work + actual.2 + 128 * (S + A + 1)⟩

theorem word_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) (entry : GeneralPaperReferenceSlotConstruction.Entry A)
    (hEntry : entry ∈ (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries) :
    (install model S A directory memory).memory entry.location.value = some (.reference ⟨A,entry.target⟩) :=
  GeneralPaperUnifiedFieldMemory.reference_read S A _ _ memory
    (GeneralPaperUnifiedDirectoryInstallation.word_keys model S A start plan directory hSafe hA hCap)
    (GeneralPaperUnifiedDirectoryInstallation.cross_keys model S A start plan directory hSafe hCovered hA hCap) entry hEntry

theorem header_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) (header : Header A) (hHeader : header ∈ directory.headers)
    (index : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory (install model S A directory memory).memory)
      header.region.reference header.fixed index.val).1 = some (⟨A,header.targets[index.val]⟩ : Word) := by
  have hRoot := GeneralPaperReferenceLayoutInstallation.roots model S A start plan directory.headers hSafe.2.1 hCap header hHeader
  apply GeneralPaperMixedReferenceRegionProgram.read_header model S A _ header hRoot _ index
  intro entry he
  exact reference_at _ _ _ (word_read model S A start plan directory memory hSafe hCovered hA hCap entry
    ((GeneralPaperReferenceRegionProgram.member model S A directory.headers entry).mpr ⟨header,hHeader,he⟩))

theorem scalar_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hCap : start + plan.sizes.sum < 2 ^ A)
    (cell : Cell A) (hCell : cell ∈ directory.cells) :
    (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory (install model S A directory memory).memory)
      cell.region.reference).1 = some cell.value ∧
      (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory (install model S A directory memory).memory)
        cell.region.reference).2 = GeneralPaperRetainedScalarValue.encode cell.value + 64 * A + 64 := by
  have h := GeneralPaperUnifiedFieldMemory.scalar_read S A
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry) memory
    (GeneralPaperFieldDirectoryInstallation.scalar_keys model S A start plan directory hSafe hPos hCap) cell.entry
    (List.mem_map.mpr ⟨cell,hCell,rfl⟩)
  have hp := scalar_at _ _ _ h
  change scalarMemory (install model S A directory memory).memory cell.region.reference.value = some cell.value at hp
  simp only [GeneralPaperPayloadMemory.read,hp,Option.elim_some,and_self]

theorem readback (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    Readback model A (install model S A directory memory) directory :=
  ⟨header_read model S A start plan directory memory hSafe hCovered hA hCap,
    scalar_read model S A start plan directory memory hSafe hPos hCap⟩

end Blotto.GeneralPaperStoredDirectoryExtension
