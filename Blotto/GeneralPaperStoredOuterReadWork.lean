import Blotto.GeneralPaperStoredGroupedInputRates

/-! Address-only prices for actual outer fields and address recovery. The
outer measured owner derives all fixed record-index capacities. No inner
rational payload precision enters these metadata bounds. -/
namespace Blotto.GeneralPaperStoredOuterReadWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperUnifiedFieldValue (referenceMemory)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def addressBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  2 * GeneralPaperEncodedScalarStorage.natBits A + 2 * GeneralPaperStoredReferenceReadWork.readBound model A A + 512 * (A + 1)

def markerBound (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredReferenceReadWork.readBound model A A + A + 128 * A + 64

theorem capacity (model : RationalCostModel) (S A start : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    3 < 2 ^ A ∧ A < 2 ^ A := by
  rw [plan_data] at hCap
  simp only [List.sum_cons,List.sum_nil] at hCap
  omega

theorem field_work (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fields : Fields A)
    (branch tag : FixedBinaryWord A)
    (hRead : Readback model A installed (GeneralPaperStoredOuterDirectory.directory A fields branch tag))
    (hRoot : installed.root = fields.record.reference) (hIndex : 3 < 2 ^ A) (index : Fin 3) :
    (GeneralPaperStoredOuterRead.field model A installed index.val).2 ≤ GeneralPaperStoredReferenceReadWork.readBound model A A := by
  exact GeneralPaperStoredReferenceReadWork.read_work model A A 0 index.val _ installed.root _ (by decide)
    (index.isLt.trans hIndex) (GeneralPaperStoredOuterRead.field_source model A installed fields branch tag hRead hRoot index)

theorem address_work (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fields : Fields A)
    (branch tag : FixedBinaryWord A)
    (hRead : Readback model A installed (GeneralPaperStoredOuterDirectory.directory A fields branch tag))
    (hRoot : installed.root = fields.record.reference) (hIndex : 3 < 2 ^ A) :
    (GeneralPaperStoredOuterRead.address model A installed).2 ≤ addressBound model A := by
  have hControl := GeneralPaperStoredOuterRead.field_source model A installed fields branch tag hRead hRoot ⟨1,by decide⟩
  have hControlWork := field_work model A installed fields branch tag hRead hRoot hIndex ⟨1,by decide⟩
  have hLoadWork := (GeneralPaperStoredChildRead.trace model A installed 0 1 fields.control.reference hControl).2
  let loaded := GeneralPaperStoredScalarRead.atRoot installed fields.control.reference
  let header : Header A := ⟨fields.control,32,[fields.value.reference]⟩
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨fields.value,.natural A⟩
  have hScalar := GeneralPaperStoredScalarRead.from_readback model A installed _ hRead header (List.mem_cons_self ..)
    cell (List.mem_singleton_self _) ⟨0,by change 0 < 1; decide⟩ rfl
  change (GeneralPaperStoredScalarRead.read model A loaded 32 0).1 = some (.natural A) ∧
    (GeneralPaperStoredScalarRead.read model A loaded 32 0).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) fields.control.reference 32 0).2 +
      GeneralPaperEncodedScalarStorage.natBits A + 192 * A + 128 at hScalar
  have hPointer := hRead.1 header (List.mem_cons_self ..) ⟨0,by change 0 < 1; decide⟩
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 32 0 _ fields.control.reference fields.value.reference
    (by decide) (Nat.two_pow_pos A) hPointer
  have hNatural := (GeneralPaperStoredScalarRead.natural_of_scalar model A loaded 32 0 A hScalar.1).2
  rw [(GeneralPaperStoredOuterRead.address_source model A installed fields branch tag hRead hRoot).2,hLoadWork,hNatural,hScalar.2]
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 1).2 ≤ _ at hControlWork
  unfold addressBound
  omega

theorem marker_work (model : RationalCostModel) (A tagValue : ℕ) (installed : Installed A) (fields : Fields A) (branch : FixedBinaryWord A)
    (hRead : Readback model A installed (GeneralPaperStoredOuterDirectory.directory A fields branch (FixedBinaryWord.ofNat A tagValue)))
    (hRoot : installed.root = fields.record.reference) (hIndex : 3 < 2 ^ A) (hTag : tagValue < 2 ^ A) :
    (GeneralPaperStoredOuterMarker.read model A installed).2 ≤ markerBound model A := by
  have hField := GeneralPaperStoredOuterRead.field_source model A installed fields branch (FixedBinaryWord.ofNat A tagValue) hRead hRoot ⟨2,by decide⟩
  have hWork := field_work model A installed fields branch (FixedBinaryWord.ofNat A tagValue) hRead hRoot hIndex ⟨2,by decide⟩
  rw [(GeneralPaperStoredOuterMarker.from_field model A A tagValue installed hField hTag).2]
  change (GeneralPaperStoredOuterRead.field model A installed 2).2 ≤ _ at hWork
  unfold markerBound
  omega

end Blotto.GeneralPaperStoredOuterReadWork
