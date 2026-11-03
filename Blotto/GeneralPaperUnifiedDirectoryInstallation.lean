import Blotto.GeneralPaperUnifiedFieldMemory

/-! A returned directory representation stores ONE reference/scalar RAM.
The legacy typed interfaces below are read projections of that same map.
Complete partitions derive cross-kind separation and preserve all old reads
within the paper indexed-storage model. -/
namespace Blotto.GeneralPaperUnifiedDirectoryInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedFieldValue
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Installed (A : ℕ) where
  memory : Memory
  root : FixedBinaryWord A
  work : ℕ

def install (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : Installed A :=
  let words := GeneralPaperReferenceRegionProgram.collect model S A directory.headers
  let actual := GeneralPaperUnifiedFieldMemory.prepare S A words.entries (directory.cells.map Cell.entry) (GeneralPaperPayloadMemory.empty Value)
  ⟨actual.1,directory.root.reference,words.work + actual.2 + 128 * (S + A + 1)⟩

def view {A : ℕ} (installed : Installed A) : GeneralPaperFieldDirectoryInstallation.Installed A :=
  ⟨referenceMemory installed.memory,scalarMemory installed.memory,installed.root,installed.work⟩

theorem word_keys (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ((GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.map (fun entry => entry.location.value)).Nodup :=
  GeneralPaperReferenceLayoutInstallation.all_keys model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1 hCap

theorem cross_keys (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    List.Disjoint ((GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.map (fun entry => entry.location.value))
      ((directory.cells.map Cell.entry).map (fun entry => entry.1.value)) := by
  simpa only [List.map_map,Cell.entry,Function.comp_def] using
    GeneralPaperFieldDirectorySeparation.cross_keys model S A start plan directory hSafe hCovered hA hCap

theorem word_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) (entry : GeneralPaperReferenceSlotConstruction.Entry A)
    (hEntry : entry ∈ (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries) :
    (install model S A directory).memory entry.location.value = some (.reference ⟨A,entry.target⟩) :=
  GeneralPaperUnifiedFieldMemory.reference_read S A _ _ (GeneralPaperPayloadMemory.empty Value)
    (word_keys model S A start plan directory hSafe hA hCap)
    (cross_keys model S A start plan directory hSafe hCovered hA hCap) entry hEntry

theorem header_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) (header : Header A) (hHeader : header ∈ directory.headers)
    (j : Fin header.targets.length) :
    (GeneralPaperMixedReferenceRegionProgram.read model A (view (install model S A directory)).references
      header.region.reference header.fixed j.val).1 = some (⟨A,header.targets[j.val]⟩ : Word) := by
  have hRoot := GeneralPaperReferenceLayoutInstallation.roots model S A start plan directory.headers hSafe.2.1 hCap header hHeader
  apply GeneralPaperMixedReferenceRegionProgram.read_header model S A _ header hRoot _ j
  intro entry he
  exact reference_at _ _ _ (word_read model S A start plan directory hSafe hCovered hA hCap entry
    ((GeneralPaperReferenceRegionProgram.member model S A directory.headers entry).mpr ⟨header,hHeader,he⟩))

theorem scalar_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hCap : start + plan.sizes.sum < 2 ^ A)
    (cell : Cell A) (hCell : cell ∈ directory.cells) :
    (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (view (install model S A directory)).payloads
      cell.region.reference).1 = some cell.value := by
  have h := GeneralPaperUnifiedFieldMemory.scalar_read S A
    (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries (directory.cells.map Cell.entry)
    (GeneralPaperPayloadMemory.empty Value)
    (GeneralPaperFieldDirectoryInstallation.scalar_keys model S A start plan directory hSafe hPos hCap) cell.entry
    (List.mem_map.mpr ⟨cell,hCell,rfl⟩)
  exact scalar_at _ _ _ h

theorem install_work (model : RationalCostModel) (S A : ℕ) (directory : Directory A) :
    (install model S A directory).work = (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).work +
      GeneralPaperReferenceHeaderSlotArea.slots directory.headers * (67 * A + 64 + 128 * (S + A + 1)) +
      2 * (directory.cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum +
      directory.cells.length * (65 * A + 64 + 128 * (S + A + 1)) + 512 * (S + A + 1) := by
  dsimp only [install]
  rw [GeneralPaperUnifiedFieldMemory.prepare_work,GeneralPaperReferenceRegionProgram.count]
  simp only [List.map_map,Cell.entry,Function.comp_def,List.length_map]
  unfold GeneralPaperReferenceHeaderSlotArea.slots
  ring

end Blotto.GeneralPaperUnifiedDirectoryInstallation
