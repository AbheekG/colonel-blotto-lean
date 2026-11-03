import Blotto.GeneralPaperStoredRejectionTrace

/-! Prepared-cache controls and the single original-budget scalar are read
from the same retained memory. Source/shape/membership arguments are erased
correspondence observers, not arguments to the executed readers. -/
namespace Blotto.GeneralPaperStoredPreparedRead
open GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def controls (model : RationalCostModel) (A : ℕ) (installed : Installed A) : GeneralPaperStoredReadStream.Result ℕ :=
  GeneralPaperStoredRecordCollectors.naturals model A installed 3

def budget (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option ℚ × ℕ :=
  GeneralPaperStoredScalarRead.rational model A installed 0 4

theorem controls_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (controls model A installed).values = some [prepared.D,prepared.rangeBits,prepared.midpointBits,prepared.midpointCount] ∧
      (controls model A installed).count = 4 ∧
      (controls model A installed).work = (GeneralPaperStoredChildRead.load model A installed 0 3).2 +
        (GeneralPaperStoredReadStream.naturals model A (GeneralPaperStoredScalarRead.atRoot installed root) 32).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨3,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .controls fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded full := hContract
  have hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A fieldStart 32 1
      ((GeneralPaperPreparedRecordCursor.controls prepared).map Scalar.natural) ∈ full.headers :=
    hHeaders _ (hChildHeaders _ (List.mem_singleton_self _))
  have hValues := GeneralPaperStoredReadStreamSources.naturals model S A fieldStart loaded full hChildContract
    (GeneralPaperPreparedRecordCursor.controls prepared) hChildRead hHeader rfl
  obtain ⟨hv,hc,hw⟩ := GeneralPaperStoredRecordCollectors.naturals_trace model A installed loaded 3 hLoad
  exact ⟨child.root.reference,hv.trans hValues.1,hc.trans hValues.2.1,hw⟩

theorem budget_source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference) :
    (budget model A installed).1 = some prepared.budget ∧
      (budget model A installed).2 = (GeneralPaperStoredScalarRead.read model A installed 0 4).2 +
        rationalWordWidth prepared.budget + 64 * A + 64 := by
  obtain ⟨fieldStart,_,hPointer,hChildRead,_,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨4,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .budget fieldStart
  let cell : GeneralPaperScalarFieldCursor.Cell A := ⟨child.root,.rational prepared.budget⟩
  have hScalar := (hChildRead.2 cell (List.mem_singleton_self _)).1
  have hv := (GeneralPaperStoredScalarRead.trace model A installed 0 4 child.root.reference (.rational prepared.budget) hPointer hScalar).1
  exact GeneralPaperStoredScalarRead.rational_of_scalar model A installed 0 4 prepared.budget hv

end Blotto.GeneralPaperStoredPreparedRead
