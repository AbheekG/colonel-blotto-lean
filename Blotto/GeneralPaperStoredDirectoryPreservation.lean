import Blotto.GeneralPaperStoredDirectoryExtension

/-! Actual extension keys are in their allocated outer owner regions.
Consequently installation preserves the entire earlier address prefix,
independently of its cell kinds and the earlier reference width. -/
namespace Blotto.GeneralPaperStoredDirectoryPreservation
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedFieldValue
open GeneralPaperFieldDirectorySafety
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def Below (bound : ℕ) (first second : Memory) : Prop := ∀ key < bound,first key = second key

theorem writes_after (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    Below start (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory memory := by
  intro key hk
  apply GeneralPaperUnifiedFieldMemory.preserves_key
  · intro entry he hEq
    obtain ⟨header,hh,hEntry⟩ := (GeneralPaperReferenceRegionProgram.member model S A directory.headers entry).mp he
    have hRegion := hSafe.2.1.subset (List.mem_map.mpr ⟨header,hh,rfl⟩)
    have hBounds := GeneralPaperMeasuredBlockLayout.range model S A start plan header.region hRegion
    have hNative := GeneralPaperReferenceRegionSlots.entry_key_in_region model S A header hA (hSafe.2.2.2.1 header hh)
      (hBounds.2.trans_lt hCap) entry hEntry
    have hLower := hNative.1
    omega
  · intro entry he hEq
    obtain ⟨cell,hCell,rfl⟩ := List.mem_map.mp he
    have hRegion := hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hCell,rfl⟩)
    have hBounds := GeneralPaperMeasuredBlockLayout.range model S A start plan cell.region hRegion
    have hRoot := GeneralPaperMeasuredBlockLayout.references model S A start plan hCap cell.region hRegion
    change cell.region.reference.value = key at hEq
    omega

theorem empty_eq (model : RationalCostModel) (S A : ℕ) (directory : Directory A) :
    GeneralPaperStoredDirectoryExtension.install model S A directory (GeneralPaperPayloadMemory.empty Value) =
      GeneralPaperUnifiedDirectoryInstallation.install model S A directory := rfl

theorem work (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) :
    (GeneralPaperStoredDirectoryExtension.install model S A directory memory).work =
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).work +
      GeneralPaperReferenceHeaderSlotArea.slots directory.headers * (67 * A + 64 + 128 * (S + A + 1)) +
      2 * (directory.cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum +
      directory.cells.length * (65 * A + 64 + 128 * (S + A + 1)) + 512 * (S + A + 1) := by
  dsimp only [GeneralPaperStoredDirectoryExtension.install]
  rw [GeneralPaperUnifiedFieldMemory.prepare_work,GeneralPaperReferenceRegionProgram.count]
  simp only [List.map_map,Cell.entry,Function.comp_def,List.length_map]
  unfold GeneralPaperReferenceHeaderSlotArea.slots
  ring

end Blotto.GeneralPaperStoredDirectoryPreservation
