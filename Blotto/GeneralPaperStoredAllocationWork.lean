import Blotto.GeneralPaperStoredPostselectionWork
import Blotto.GeneralPaperStoredSamplerRejectionWork
import Blotto.GeneralPaperStoredAllocationLaw

/-! Complete actual stored allocation work joins first-success rejection
with one full postselection/output pass. Fair-trace integration charges the
postselection bound once, with no truncation fallback or stopping oracle. -/
namespace Blotto.GeneralPaperStoredAllocationWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def expectedBound (model : RationalCostModel) (A s b c : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  GeneralPaperStoredSamplerRejectionWork.expectedBound model A sampler.prepared.rangeBits
    (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length +
    GeneralPaperStoredPostselectionWork.bound model A s b c sampler.prepared + 128 * (A + 1)

theorem postselection_join (model : RationalCostModel) (S A start s b c : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredAllocationDraw.run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      (GeneralPaperStoredSamplerRejection.run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)).work +
        GeneralPaperStoredPostselectionWork.bound model A s b c sampler.prepared + 128 * (A + 1) := by
  obtain ⟨_,hData,_,_⟩ := GeneralPaperStoredSamplerRejection.source model S A start installed sampler ctx.contract hRoot ctx.positive ctx.capacity cap tape
  unfold GeneralPaperStoredAllocationDraw.run
  dsimp only
  rw [hData]
  cases hResult : (GeneralPaperEqualRejectionPrefix.blockRun sampler.prepared.D cap tape).output with
  | none => simp only [Option.map_none]; omega
  | some rank =>
    have hPost := GeneralPaperStoredPostselectionWork.work model S A start s b c installed sampler ctx hRoot hs h hB hc hC
      (GeneralPaperEqualPreparedCache.select sampler.prepared rank) fresh
    simp only [Option.map_some]
    omega

theorem finite_work (model : RationalCostModel) (S A start s b c : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (cap : ℕ) (tape : ℕ → Fin (UniformNatRejection.width sampler.prepared.D) → Bool) (fresh : Fin sampler.prepared.midpointBits → Bool) :
    (GeneralPaperStoredAllocationDraw.run model A installed cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).work ≤
      cap * GeneralPaperStoredRejectionWork.perAttempt model A sampler.prepared.rangeBits
        (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length +
      GeneralPaperStoredSamplerRejectionWork.entryBound model A +
      GeneralPaperStoredPostselectionWork.bound model A s b c sampler.prepared + 128 * (A + 1) := by
  have hJoin := postselection_join model S A start s b c installed sampler ctx hRoot hs h hB hc hC cap tape fresh
  have hReject := GeneralPaperStoredSamplerRejectionWork.work model S A start installed sampler ctx hRoot cap
    (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
  omega

theorem expected_work (model : RationalCostModel) (S A start s b c : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c) :
    (∫⁻ trace, ((GeneralPaperStoredAllocationLaw.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤
      (expectedBound model A s b c sampler : ℝ≥0∞) := by
  let P := GeneralPaperStoredPostselectionWork.bound model A s b c sampler.prepared + 128 * (A + 1)
  have hPoint (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
      (GeneralPaperStoredAllocationLaw.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work ≤
        (GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work + P := by
    have hPrice := postselection_join model S A start s b c installed sampler ctx hRoot hs h hB hc hC (trace.1 + 1)
      (GeneralPaperEqualBooleanTraceCost.tapeFor sampler.prepared.D sampler.prepared.midpointBits trace)
      (scalar sampler.prepared.D sampler.prepared.midpointBits trace.1 trace.2)
    rw [GeneralPaperStoredRejectionTrace.blocks_eq] at hPrice
    simpa only [GeneralPaperStoredAllocationLaw.observed,GeneralPaperStoredRejectionTrace.observed,P,Nat.add_assoc] using hPrice
  have hReject := GeneralPaperStoredSamplerRejectionWork.expected_work model S A start sampler.prepared.midpointBits installed sampler ctx hRoot
  calc
    _ ≤ ∫⁻ trace, (((GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work + P : ℕ) : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)) :=
      lintegral_mono (fun trace => (show ((GeneralPaperStoredAllocationLaw.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞) ≤
        (((GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work + P : ℕ) : ℝ≥0∞) by exact_mod_cast hPoint trace))
    _ = (∫⁻ trace, ((GeneralPaperStoredRejectionTrace.observed model A installed sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) + P := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ (GeneralPaperStoredSamplerRejectionWork.expectedBound model A sampler.prepared.rangeBits
        (GeneralPaperPositiveSegmentCompaction.count l) sampler.categorical.rows.length : ℝ≥0∞) + P := add_le_add hReject le_rfl
    _ = _ := by simp only [expectedBound,P,Nat.cast_add,add_assoc]

theorem native_expected {n : ℕ} (bits : Bool) (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget).address)
    (hReturn : (GeneralPaperCountedSamplerInstallation.build model S
      (GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget)).values = some returned) :
    let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
    (∫⁻ trace, ((GeneralPaperStoredAllocationLaw.observed model source.address returned source.prepared.D source.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law source.prepared.D source.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive source.prepared) :
        Measure (Trace source.prepared.D source.prepared.midpointBits))) ≤
      (expectedBound model source.address (GeneralPaperEqualNativeSampler.segmentHeight n k) (rationalWordWidth budget)
        (binaryWordWidth n + k + 9) source : ℝ≥0∞) := by
  dsimp only
  let source := GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget
  have ctx := GeneralPaperStoredReadContext.native_return bits model W S k values v hv small budget returned hReturn
  obtain ⟨hA,hCap⟩ := GeneralPaperStoredNativeConstruction.native_bounds bits model W S k values v hv small budget
  obtain ⟨output,hBuilt,_,_,hRoot,_⟩ := GeneralPaperCountedSamplerInstallation.build_source model S source hA hCap
  have hEq : output = returned := Option.some.inj (hBuilt.symm.trans hReturn)
  subst output
  have hs : 2 ≤ GeneralPaperEqualNativeSampler.segmentHeight n k := by
    unfold GeneralPaperEqualNativeSampler.segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
    omega
  exact expected_work model S source.address 0 _ _ _ returned source ctx hRoot hs
    (GeneralPaperEqualNativeSampler.native_lottery_height bits model W k values v hv small)
    (rationalHeight_of_wordWidth budget) (by omega) (GeneralPaperEqualNativeCache.route_height bits model W k values v hv small budget)

end Blotto.GeneralPaperStoredAllocationWork
