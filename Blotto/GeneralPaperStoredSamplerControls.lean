import Blotto.GeneralPaperStoredRecordCollectors

/-! Exponent/address controls are actually read from the installed sampler
root. Every successful source-only constructor return supports this read;
source controls and widths are never execution arguments to the reader. -/
namespace Blotto.GeneralPaperStoredSamplerControls
open GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def read (model : RationalCostModel) (A : ℕ) (installed : Installed A) : GeneralPaperStoredReadStream.Result ℕ :=
  GeneralPaperStoredRecordCollectors.naturals model A installed 2

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference) :
    ∃ root : FixedBinaryWord A,
      (read model A installed).values = some [sampler.exponent,sampler.address] ∧
      (read model A installed).count = 2 ∧
      (read model A installed).work = (GeneralPaperStoredChildRead.load model A installed 0 2).2 +
        (GeneralPaperStoredReadStream.naturals model A (GeneralPaperStoredScalarRead.atRoot installed root) 32).work + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨2,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .controls fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  have hHeader : GeneralPaperRetainedHeaderCountSources.listHeader model S A fieldStart 32 1
      ((GeneralPaperSamplerRecordCursor.controls sampler).map Scalar.natural) ∈
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start).headers := hHeaders _ (List.mem_singleton_self _)
  have hValues := GeneralPaperStoredReadStreamSources.naturals model S A fieldStart loaded _ hChildContract
    (GeneralPaperSamplerRecordCursor.controls sampler) hChildRead hHeader rfl
  obtain ⟨hv,hc,hw⟩ := GeneralPaperStoredRecordCollectors.naturals_trace model A installed loaded 2 hLoad
  exact ⟨child.root.reference,hv.trans hValues.1,hc.trans hValues.2.1,hw⟩

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned) :
    ∃ root : FixedBinaryWord sampler.address,
      (read model sampler.address returned).values = some [sampler.exponent,sampler.address] ∧
      (read model sampler.address returned).count = 2 ∧
      (read model sampler.address returned).work = (GeneralPaperStoredChildRead.load model sampler.address returned 0 2).2 +
        (GeneralPaperStoredReadStream.naturals model sampler.address (GeneralPaperStoredScalarRead.atRoot returned root) 32).work +
        128 * sampler.address + 64 := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact source model S sampler.address 0 returned sampler hContract hRoot

end Blotto.GeneralPaperStoredSamplerControls
