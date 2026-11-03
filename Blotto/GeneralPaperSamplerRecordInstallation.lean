import Blotto.GeneralPaperSamplerRecordCursor

/-! Complete retained-field installation in one indexed memory. Every actual
header slot and scalar cell reads back with its local payload-sensitive price.
The source-only builder executes measurement/layout once, then extraction and
installation once. Full draw/refinement and sharp resource joins remain open. -/
namespace Blotto.GeneralPaperSamplerRecordInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUnifiedMatrixInstallation (finish Result)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def Readback (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A) : Prop :=
  (∀ header ∈ directory.headers,∀ index : Fin header.targets.length,
    (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory)
      header.region.reference header.fixed index.val).1 = some (⟨A,header.targets[index.val]⟩ : Word)) ∧
  ∀ cell ∈ directory.cells,
    (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) cell.region.reference).1 = some cell.value ∧
    (GeneralPaperPayloadMemory.read A GeneralPaperRetainedScalarValue.encode (scalarMemory installed.memory) cell.region.reference).2 =
      GeneralPaperRetainedScalarValue.encode cell.value + 64 * A + 64

theorem installation_readback (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    Readback model A (GeneralPaperUnifiedDirectoryInstallation.install model S A directory) directory := by
  constructor
  · intro header hh index
    exact GeneralPaperUnifiedDirectoryInstallation.header_read model S A start plan directory hSafe hCovered hA hCap header hh index
  · intro cell hc
    have h := GeneralPaperUnifiedDirectoryInstallation.scalar_read model S A start plan directory hSafe hPos hCap cell hc
    change scalarMemory (GeneralPaperUnifiedDirectoryInstallation.install model S A directory).memory cell.region.reference.value = some cell.value at h
    simp only [GeneralPaperPayloadMemory.read,h,Option.elim_some,and_self]

def run (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (regions : List (Region A)) : Result A :=
  let parsed := GeneralPaperSamplerRecordCursor.run model S A source regions
  match parsed.values with
  | none => ⟨none,parsed.remaining,parsed.work + 64 * (S + A + 1)⟩
  | some directory =>
    let actual := finish model S A parsed.work directory
    ⟨some actual,parsed.remaining,actual.work⟩

theorem on_parsed (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (regions : List (Region A)) (directory : Directory A)
    (hParsed : (GeneralPaperSamplerRecordCursor.run model S A source regions).values = some directory) :
    (run model S A source regions).values = some (finish model S A (GeneralPaperSamplerRecordCursor.run model S A source regions).work directory) ∧
      (run model S A source regions).remaining = (GeneralPaperSamplerRecordCursor.run model S A source regions).remaining ∧
      (run model S A source regions).work = (finish model S A (GeneralPaperSamplerRecordCursor.run model S A source regions).work directory).work := by
  simp only [run,hParsed,and_self]

theorem sampler_prefix (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest
    ∃ output : Installed A,(run model S A source regions).values = some output ∧
      (run model S A source regions).remaining = rest ∧ output.work = (run model S A source regions).work ∧
      output.root = (GeneralPaperSamplerRecordCursor.expected model S A source start).root.reference ∧
      Readback model A output (GeneralPaperSamplerRecordCursor.expected model S A source start) := by
  dsimp only
  let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest
  let directory := GeneralPaperSamplerRecordCursor.expected model S A source start
  obtain ⟨hParsed,hRemaining,hs,hc⟩ := GeneralPaperSamplerRecordCursor.success model S A start source rest
  obtain ⟨hv,hr,hw⟩ := on_parsed model S A source regions directory hParsed
  exact ⟨_,hv,hr.trans hRemaining,hw.symm,rfl,installation_readback model S A start _ directory hs hc
    (GeneralPaperEqualMeasuredPlanPositive.sampler model S A source hA) hA hCap⟩

def attach (S A prefixWork : ℕ) (output : Installed A) : Installed A :=
  ⟨output.memory,output.root,prefixWork + output.work + 64 * (S + A + 1)⟩

def build (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : Result source.address :=
  let A := source.address
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source
  let layout := GeneralPaperMeasuredBlockLayout.run model S A 0 plan
  let actual := run model S A source layout.1
  match actual.values with
  | none => ⟨none,actual.remaining,layout.2.2 + actual.work + 64 * (S + A + 1)⟩
  | some output =>
    let finished := attach S A layout.2.2 output
    ⟨some finished,actual.remaining,finished.work⟩

theorem build_on_return (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (output : Installed source.address)
    (hReturn : (run model S source.address source
      (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).values = some output) :
    (build model S source).values = some (attach S source.address
      (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).2.2 output) ∧
      (build model S source).remaining = (run model S source.address source
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).1).remaining ∧
      (build model S source).work = (attach S source.address
        (GeneralPaperMeasuredBlockLayout.run model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)).2.2 output).work := by
  simp only [build,hReturn,and_self]

theorem build_source (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hA : 0 < source.address)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address) :
    ∃ output : Installed source.address,(build model S source).values = some output ∧
      (build model S source).remaining = [] ∧ output.work = (build model S source).work ∧
      output.root = (GeneralPaperSamplerRecordCursor.expected model S source.address source 0).root.reference ∧
      Readback model source.address output (GeneralPaperSamplerRecordCursor.expected model S source.address source 0) := by
  obtain ⟨output,hRun,hRemaining,_,hRoot,hRead⟩ := sampler_prefix model S source.address 0 source [] hA (by simpa only [Nat.zero_add] using hCap)
  simp only [List.append_nil] at hRun hRemaining
  obtain ⟨hv,hr,hw⟩ := build_on_return model S source output hRun
  exact ⟨_,hv,hr.trans hRemaining,hw.symm,hRoot,hRead⟩

end Blotto.GeneralPaperSamplerRecordInstallation
