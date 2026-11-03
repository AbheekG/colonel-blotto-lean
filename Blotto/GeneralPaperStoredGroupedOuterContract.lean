import Blotto.GeneralPaperStoredGroupedOuterLaw

/-! The actual native grouped outer constructor and its continuous-game
contract share one returned memory. Both retained capacities are derived;
no caller-supplied layout, address or storage-fit premise is needed. -/
namespace Blotto.GeneralPaperStoredGroupedOuterContract
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

theorem native_refines {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget)).values = some returned) :
    GeneralPaperStoredGroupedOuterDraw.Refines model
      ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1) returned
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget) := by
  obtain ⟨hInner,hOuter⟩ := GeneralPaperStoredGroupedOuterNative.bounds model W S k values v hv small budget
  exact GeneralPaperStoredGroupedOuterConstruction.every_returned model S _ hInner hOuter returned hReturn

theorem native_law {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (returned : Installed ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget)).values = some returned) :
    let sampler := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
    GeneralPaperStoredGroupedOuterLaw.outputLaw n model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits
      (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) = GeneralPaperEqualStoredBitSampler.outputLaw sampler model :=
  GeneralPaperStoredGroupedOuterLaw.output_law_source model _ returned _
    (native_refines model W S k values v hv small budget returned hReturn)

theorem native_epsilon {n : ℕ} (model : RationalCostModel) (W S : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (eps : ℚ) (hPositive : 0 < eps) (hOne : eps < 1)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W
      (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1) (budget : ℚ) (hBudget : 0 < budget) :
    let sampler := GeneralPaperEqualStoredBitSampler.native true model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
    ∃ returned : Installed (sampler.address + 1),
      (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned ∧
      (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).remaining = [] ∧
      returned.work = (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).work ∧
      let μ := GeneralPaperStoredGroupedOuterLaw.outputLaw n model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits
        (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared)
      Supported (budget : ℝ) μ ∧ regret v.values (budget : ℝ) μ μ ≤ (eps : ℝ) := by
  dsimp only
  obtain ⟨returned,hReturn,hRemaining,hWork,_⟩ := GeneralPaperStoredGroupedOuterNative.constructed model W S
    (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget
  refine ⟨returned,hReturn,hRemaining,hWork,?_⟩
  rw [native_law model W S _ values v hv small budget returned hReturn]
  exact GeneralPaperEqualStoredBitSampler.native_epsilon true model W values v hv eps hPositive hOne small budget hBudget

theorem native_written_output {n b : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (small : ∀ j,2 * (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight j ≤ 1)
    (budget : ℚ) (hBudget : 0 ≤ budget) (hHeight : RationalHeight budget b)
    (returned : Installed ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget)).values = some returned)
    (cap : ℕ)
    (tape : ℕ → Fin (UniformNatRejection.width
      (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).prepared.D) → Bool)
    (fresh : Fin (k + 5) → Bool) (row : Array ℚ)
    (hOutput : (GeneralPaperStoredGroupedOuterDraw.run model
      ((GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).address + 1) returned cap
      (GeneralPaperStoredBooleanRejection.blocks
        (GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget).prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output = some row) :
    row.size = n ∧ FullBudget (budget : ℝ) (fun j : Fin n => (row.getD j.val 0 : ℝ)) ∧
      ∀ j : Fin n, RationalHeight (row.getD j.val 0) (33554432 * (b + binaryWordWidth n + k + 10)) := by
  let sampler := GeneralPaperEqualStoredBitSampler.native true model W k values v hv small budget
  have hRefines := native_refines model W S k values v hv small budget returned hReturn
  obtain ⟨source,hSource,hData⟩ := GeneralPaperStoredGroupedOuterLaw.completed_row model _ returned sampler hRefines cap tape fresh row hOutput
  have hWritten := GeneralPaperEqualFullBitOutput.native_written_output true model W k values v hv small budget hBudget hHeight cap tape fresh source hSource
  rw [← hData]
  refine ⟨source.size,?_,?_⟩
  · rw [GeneralPaperStoredAllocationLaw.array_real]
    exact hWritten.1
  · intro j
    have hj : j.val < source.data.size := by rw [source.size]; exact j.isLt
    simpa [Array.getD,hj,RationalResourceArray.allocation] using hWritten.2 j

end Blotto.GeneralPaperStoredGroupedOuterContract
