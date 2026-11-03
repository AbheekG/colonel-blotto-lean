import Blotto.GeneralPaperStoredDirectoryPreservation

/-! Agreement on the actual inner address extent preserves header/scalar
readback and initialized counts, even if the extending installer uses a
different reference width. No source-memory equality oracle is executed. -/
namespace Blotto.GeneralPaperStoredReadbackPreservation
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperSequentialLayout
open GeneralPaperUnifiedFieldValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperFieldDirectorySafety
open GeneralPaperStoredDirectoryPreservation (Below)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

theorem readback (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (before after : Installed A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (hRead : Readback model A before directory)
    (hAgree : Below (start + plan.sizes.sum) after.memory before.memory) : Readback model A after directory := by
  constructor
  · intro header hh index
    have hRegion := hSafe.2.1.subset (List.mem_map.mpr ⟨header,hh,rfl⟩)
    have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan header.region hRegion
    have hRoot := GeneralPaperMeasuredBlockLayout.references model S A start plan hCap header.region hRegion
    have hValid := hSafe.2.2.2.1 header hh
    have hMul := Nat.mul_le_mul_left A (Nat.succ_le_of_lt index.isLt)
    have hPosition : header.region.start + A * (header.fixed + index.val) < header.region.stop := by
      unfold Valid at hValid
      unfold Region.stop
      nlinarith
    have hFits : header.region.start + A * (header.fixed + index.val) < 2 ^ A :=
      hPosition.trans_le hRange.2 |>.trans hCap
    let key := (FixedBinaryWord.ofNat A (header.region.reference.value + A * (header.fixed + 1 * index.val + 0))).value
    have hKey : key < start + plan.sizes.sum := by
      dsimp only [key]
      rw [hRoot]
      simp only [Nat.one_mul,Nat.add_zero]
      rw [FixedBinaryWord.value_ofNat A _ hFits]
      exact hPosition.trans_le hRange.2
    have hWord : referenceMemory after.memory key = referenceMemory before.memory key := by
      unfold referenceMemory
      rw [hAgree key hKey]
    have h := hRead.1 header hh index
    simp only [GeneralPaperMixedReferenceRegionProgram.read_data] at h ⊢
    exact hWord.trans h
  · intro cell hc
    have hRegion := hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)
    have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan cell.region hRegion
    have hRoot := GeneralPaperMeasuredBlockLayout.references model S A start plan hCap cell.region hRegion
    have hPositive : 0 < cell.region.length := by
      rw [hSafe.2.2.2.2 cell hc]
      exact GeneralPaperRetainedScalarValue.positive cell.value
    have hKey : cell.region.reference.value < start + plan.sizes.sum := by
      rw [hRoot]
      unfold Region.stop at hRange
      omega
    have hScalar : scalarMemory after.memory cell.region.reference.value = scalarMemory before.memory cell.region.reference.value := by
      unfold scalarMemory
      rw [hAgree _ hKey]
    simpa only [GeneralPaperPayloadMemory.read,hScalar] using hRead.2 cell hc

theorem contract (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (before after : Installed A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (hContract : Contract model A before directory)
    (hAgree : Below (start + plan.sizes.sum) after.memory before.memory) : Contract model A after directory := by
  have hNew := readback model S A start plan (GeneralPaperHeaderCountDirectory.expanded directory) before after
    (GeneralPaperHeaderCountDirectory.safe _ directory hSafe) hA hCap hContract.1 hAgree
  refine ⟨hNew,GeneralPaperHeaderCountReadback.compatible model A after directory hNew,?_⟩
  intro header hh hf
  have hBounds := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap header hh
  exact GeneralPaperHeaderCountReadback.count_source model A after directory hNew header hh hf
    (GeneralPaperHeaderCountExpansion.count_fits header hA (hSafe.2.2.2.1 header hh) hBounds)

end Blotto.GeneralPaperStoredReadbackPreservation
