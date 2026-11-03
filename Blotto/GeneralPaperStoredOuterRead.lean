import Blotto.GeneralPaperStoredOuterDirectory

/-! Outer field/address reads use the same combined memory as the inner
sampler. Address recovery follows the actual record/control/scalar pointers. -/
namespace Blotto.GeneralPaperStoredOuterRead
open GeneralPaperFieldDirectory GeneralPaperReferenceRegionSlots GeneralPaperEqualOuterFieldLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def field (model : RationalCostModel) (A : ℕ) (installed : Installed A) (index : ℕ) : Option Word × ℕ :=
  GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) installed.root 0 index

def address (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℕ × ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 1
  match child.1 with
  | none => (none,child.2 + 64 * (A + 1))
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredScalarRead.natural model B loaded 32 0
    (actual.1,child.2 + actual.2 + 64 * (A + B + 1))

theorem field_source (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fields : Fields A) (branch tag : FixedBinaryWord A)
    (hRead : Readback model A installed (GeneralPaperStoredOuterDirectory.directory A fields branch tag))
    (hRoot : installed.root = fields.record.reference) (index : Fin 3) :
    (field model A installed index.val).1 = some (⟨A,([branch,fields.control.reference,tag][index.val]'index.isLt)⟩ : Word) := by
  let header : Header A := ⟨fields.record,0,[branch,fields.control.reference,tag]⟩
  have hh : header ∈ (GeneralPaperStoredOuterDirectory.directory A fields branch tag).headers := List.mem_cons_of_mem _ (List.mem_cons_self ..)
  have h := hRead.1 header hh index
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) fields.record.reference 0 index.val).1 = _ at h
  rw [← hRoot] at h
  exact h

theorem address_source (model : RationalCostModel) (A : ℕ) (installed : Installed A) (fields : Fields A) (branch tag : FixedBinaryWord A)
    (hRead : Readback model A installed (GeneralPaperStoredOuterDirectory.directory A fields branch tag))
    (hRoot : installed.root = fields.record.reference) :
    (address model A installed).1 = some A ∧ (address model A installed).2 =
      (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
      (GeneralPaperStoredScalarRead.natural model A (GeneralPaperStoredScalarRead.atRoot installed fields.control.reference) 32 0).2 + 128 * A + 64 := by
  have hp := field_source model A installed fields branch tag hRead hRoot ⟨1,by decide⟩
  have hLoad := (GeneralPaperStoredChildRead.trace model A installed 0 1 fields.control.reference hp).1
  let header : Header A := ⟨fields.control,32,[fields.value.reference]⟩
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨fields.value,.natural A⟩
  have hScalar := GeneralPaperStoredScalarRead.from_readback model A installed _ hRead header (List.mem_cons_self ..)
    cell (List.mem_singleton_self _) ⟨0,by change 0 < 1; decide⟩ rfl
  have hNatural := (GeneralPaperStoredScalarRead.natural_of_scalar model A
    (GeneralPaperStoredScalarRead.atRoot installed fields.control.reference) 32 0 A hScalar.1).1
  simp only [address,hLoad,hNatural]
  constructor
  · exact True.intro
  · ring

end Blotto.GeneralPaperStoredOuterRead
