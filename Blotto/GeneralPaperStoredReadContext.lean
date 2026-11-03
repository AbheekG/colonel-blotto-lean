import Blotto.GeneralPaperStoredNativeReadRates

/-! Erased access context for actual installed memory: initialized readback,
measured ownership and address capacity. It is never an execution input.
Following a root in that memory preserves this same enclosing context. -/
namespace Blotto.GeneralPaperStoredReadContext
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperReferenceRegionSlots (Header)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

structure Context (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) : Prop where
  contract : GeneralPaperHeaderCountInstallation.Contract model A installed full
  safe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 full
  positive : 0 < A
  capacity : start + plan.sizes.sum < 2 ^ A

theorem atRoot {model : RationalCostModel} {S A start : ℕ} {plan : GeneralPaperMeasuredBlockPlan.Plan}
    {full : Directory A} {installed : Installed A} (ctx : Context model S A start plan full installed) (root : FixedBinaryWord A) :
    Context model S A start plan full (GeneralPaperStoredScalarRead.atRoot installed root) :=
  ⟨ctx.contract,ctx.safe,ctx.positive,ctx.capacity⟩

theorem header_capacity {model : RationalCostModel} {S A start : ℕ} {plan : GeneralPaperMeasuredBlockPlan.Plan}
    {full : Directory A} {installed : Installed A} (ctx : Context model S A start plan full installed)
    (header : Header A) (hHeader : header ∈ full.headers) : header.region.stop < 2 ^ A :=
  GeneralPaperReferenceLayoutInstallation.capacities model S A start plan full.headers ctx.safe.2.1 ctx.capacity header hHeader

theorem header_count_fits {model : RationalCostModel} {S A start : ℕ} {plan : GeneralPaperMeasuredBlockPlan.Plan}
    {full : Directory A} {installed : Installed A} (ctx : Context model S A start plan full installed)
    (header : Header A) (hHeader : header ∈ full.headers) : header.targets.length < 2 ^ A :=
  GeneralPaperHeaderCountExpansion.count_fits header ctx.positive (ctx.safe.2.2.2.1 header hHeader)
    (header_capacity ctx header hHeader)

theorem native_return {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    Context model S source.address 0 (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source)
      (GeneralPaperSamplerRecordCursor.expected model S source.address source 0) returned := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  exact ⟨GeneralPaperCountedSamplerInstallation.every_returned_contract model S source hA hCap returned hReturn,
    (GeneralPaperSamplerRecordCursor.success model S source.address 0 source []).2.2.1,hA,by simpa only [Nat.zero_add] using hCap⟩

end Blotto.GeneralPaperStoredReadContext
