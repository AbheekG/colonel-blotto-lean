import Blotto.GeneralPaperStoredBooleanRejection

/-! The actual sampler root reaches its Boolean cache once, then observes
stored first-success rejection. Source-only constructor returns refine the
canonical uniform rejection runner, retaining reads and exact local work. -/
namespace Blotto.GeneralPaperStoredSamplerRejection
open GeneralPaperFieldDirectory
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualBooleanRejection (Result)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run (model : RationalCostModel) (A : ℕ) (installed : Installed A) (cap : ℕ) (tape : ℕ → List Bool) : Result ℕ :=
  let child := GeneralPaperStoredChildRead.load model A installed 0 1
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,loaded⟩ =>
    let actual := GeneralPaperStoredBooleanRejection.run model B loaded cap tape
    ⟨actual.output,actual.reads,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem trace (model : RationalCostModel) (A : ℕ) (installed loaded : Installed A) (cap : ℕ) (tape : ℕ → List Bool)
    (hChild : (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : Child)) :
    (run model A installed cap tape).output = (GeneralPaperStoredBooleanRejection.run model A loaded cap tape).output ∧
      (run model A installed cap tape).reads = (GeneralPaperStoredBooleanRejection.run model A loaded cap tape).reads ∧
      (run model A installed cap tape).work = (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
        (GeneralPaperStoredBooleanRejection.run model A loaded cap tape).work + 128 * A + 64 := by
  simp only [run,hChild]
  refine ⟨True.intro,True.intro,?_⟩
  ring

theorem source (model : RationalCostModel) (S A start : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hContract : Contract model A installed (GeneralPaperSamplerRecordCursor.expected model S A sampler start))
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler).sizes.sum < 2 ^ A)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool) :
    ∃ root : FixedBinaryWord A,
      (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).output =
        (GeneralPaperEqualRejectionPrefix.blockRun sampler.prepared.D cap tape).output.map
          (fun rank => (GeneralPaperEqualPreparedCache.select sampler.prepared rank).val) ∧
      (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).reads =
        (GeneralPaperEqualRejectionPrefix.blockRun sampler.prepared.D cap tape).reads ∧
      (run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).work =
        (GeneralPaperStoredChildRead.load model A installed 0 1).2 +
          GeneralPaperStoredBooleanRejection.price model A (GeneralPaperStoredScalarRead.atRoot installed root) sampler.categorical cap tape + 128 * A + 64 := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields hContract.2.1 hRoot ⟨1,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .boolean fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hChildContract : Contract model A loaded (GeneralPaperSamplerRecordCursor.expected model S A sampler start) := hContract
  have hSafe := (GeneralPaperSamplerRecordCursor.success model S A start sampler []).2.2.1
  have hCorrect := GeneralPaperStoredBooleanTrialSource.from_directory model S A start fieldStart loaded _
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler) hChildContract hSafe hA hCap sampler.categorical hRead hHeaders rfl
  obtain ⟨hData,hReads⟩ := GeneralPaperStoredBooleanRejection.block_source model A loaded sampler.categorical hCorrect cap tape
  have hPrice := (GeneralPaperStoredBooleanRejection.source model A loaded sampler.categorical hCorrect cap tape).2.2
  obtain ⟨hv,hr,hw⟩ := trace model A installed loaded cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape) hLoad
  rw [hPrice] at hw
  exact ⟨child.root.reference,hv.trans hData,hr.trans hReads,hw⟩

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < sampler.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (returned : Installed sampler.address) (hReturn : (GeneralPaperCountedSamplerInstallation.build model S sampler).values = some returned)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool) :
    ∃ root : FixedBinaryWord sampler.address,
      (run model sampler.address returned cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).output =
        (GeneralPaperEqualRejectionPrefix.blockRun sampler.prepared.D cap tape).output.map
          (fun rank => (GeneralPaperEqualPreparedCache.select sampler.prepared rank).val) ∧
      (run model sampler.address returned cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).reads =
        (GeneralPaperEqualRejectionPrefix.blockRun sampler.prepared.D cap tape).reads ∧
      (run model sampler.address returned cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).work =
        (GeneralPaperStoredChildRead.load model sampler.address returned 0 1).2 +
          GeneralPaperStoredBooleanRejection.price model sampler.address (GeneralPaperStoredScalarRead.atRoot returned root) sampler.categorical cap tape +
            128 * sampler.address + 64 := by
  obtain ⟨output,hBuilt,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.build_source model S sampler hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  exact source model S sampler.address 0 returned sampler hContract hRoot hA (by simpa only [Nat.zero_add] using hCap) cap tape

end Blotto.GeneralPaperStoredSamplerRejection
