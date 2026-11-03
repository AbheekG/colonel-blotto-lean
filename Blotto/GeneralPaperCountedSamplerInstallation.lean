import Blotto.GeneralPaperHeaderCountInstallation

/-! One source-only sampler constructor initializes header counts before its
one memory installation. All original slot/scalar readbacks and actual count
reads share the returned memory, root, continuation and complete work. -/
namespace Blotto.GeneralPaperCountedSamplerInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedMatrixInstallation (Result)
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperSamplerRecordCursor.run model S A source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let output := GeneralPaperHeaderCountInstallation.finish model S A parsed.work directory
    ⟨some output,parsed.remaining,output.work⟩

theorem on_parsed (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (regions : List (Region A)) (directory : Directory A)
    (hParsed : (GeneralPaperSamplerRecordCursor.run model S A source regions).values = some directory) :
    (run model S A source regions).values = some (GeneralPaperHeaderCountInstallation.finish model S A
      (GeneralPaperSamplerRecordCursor.run model S A source regions).work directory) ∧
      (run model S A source regions).remaining = (GeneralPaperSamplerRecordCursor.run model S A source regions).remaining ∧
      (run model S A source regions).work = (GeneralPaperHeaderCountInstallation.finish model S A
        (GeneralPaperSamplerRecordCursor.run model S A source regions).work directory).work := by
  simp only [run,hParsed,and_self]

theorem sampler_prefix (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperSamplerRecordCursor.expected model S A source start).root.reference ∧
      Contract model A output (GeneralPaperSamplerRecordCursor.expected model S A source start) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest
  let directory := GeneralPaperSamplerRecordCursor.expected model S A source start
  obtain ⟨hParsed,hRemaining,hs,hc⟩ := GeneralPaperSamplerRecordCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  refine ⟨_,hv,hr.trans hRemaining,hw.symm,GeneralPaperHeaderCountInstallation.root model S A _ directory,?_⟩
  exact GeneralPaperHeaderCountInstallation.contract model S A start _ _ directory hs hc
    (GeneralPaperEqualMeasuredPlanPositive.sampler model S A source hA) hA hCap

def build (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : Result source.address :=
  let A := source.address
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source
  let layout := GeneralPaperMeasuredBlockLayout.run model S A 0 plan
  let actual := run model S A source layout.1
  match actual.values with
  | none => ⟨none,actual.remaining,layout.2.2 + actual.work + 64 * (S + A + 1)⟩
  | some output =>
    let finished := GeneralPaperSamplerRecordInstallation.attach S A layout.2.2 output
    ⟨some finished,actual.remaining,finished.work⟩

theorem build_on_return (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (output : Installed source.address)
    (hReturn : (run model S source.address source
      (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).values = some output) :
    (build model S source).values = some (GeneralPaperSamplerRecordInstallation.attach S source.address
      (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).2.2 output) ∧
      (build model S source).remaining = (run model S source.address source
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).remaining ∧
      (build model S source).work = (GeneralPaperSamplerRecordInstallation.attach S source.address
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).2.2 output).work := by
  simp only [build,hReturn,and_self]

theorem build_source (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    ∃ output : Installed source.address,(build model S source).values = some output ∧
      (build model S source).remaining = [] ∧ output.work = (build model S source).work ∧
      output.root = (GeneralPaperSamplerRecordCursor.expected model S source.address source 0).root.reference ∧
      Contract model source.address output (GeneralPaperSamplerRecordCursor.expected model S source.address source 0) := by
  obtain ⟨output,hRun,hRemaining,_,hRoot,hContract⟩ := sampler_prefix model S source.address 0 source [] hA (by simpa only [Nat.zero_add] using hCap)
  simp only [List.append_nil] at hRun hRemaining
  obtain ⟨hv,hr,hw⟩ := build_on_return model S source output hRun
  exact ⟨_,hv,hr.trans hRemaining,hw.symm,hRoot,hContract⟩

theorem every_returned_contract (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (returned : Installed source.address) (hReturn : (build model S source).values = some returned) :
    Contract model source.address returned (GeneralPaperSamplerRecordCursor.expected model S source.address source 0) := by
  obtain ⟨output,hRun,_,_,_,hContract⟩ := build_source model S source hA hCap
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact hContract

end Blotto.GeneralPaperCountedSamplerInstallation
