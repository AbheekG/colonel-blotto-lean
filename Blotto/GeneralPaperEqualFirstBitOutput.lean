import Blotto.GeneralPaperEqualFirstBitSampling

/-! Rational coordinate sizes for every completed draw from the current
paper's actual equal-budget source. Original budget precision is additive;
accuracy-encoding length does not enter the written-coordinate bound. -/
namespace Blotto.GeneralPaperEqualFirstBitOutput
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualBitBranch (Prepared)
open GeneralPaperEqualBitBranchDraw (Trace observed)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem height_bound (n k b : ℕ) :
    expressionHeightBudget (max (binaryWordWidth n+k+10)
      (GeneralPaperEqualCachedEmission.scaledHeight (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) (k+5) b)) 1 ≤
      GeneralPaperEqualBitDrawRates.word n (k+1) b := by
  have ho := GeneralPaperEqualBitPostprocessing.output_height
    (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) (k+5)
  have hm : GeneralPaperEqualBitPostprocessing.height
      (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) (k+5) ≤
      GeneralPaperEqualBitPostprocessing.height
        (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+(k+1)+9) ((k+1)+5) := by
    unfold GeneralPaperEqualBitPostprocessing.height GeneralPaperEqualBitPostprocessing.base expressionHeightBudget
    omega
  have hw := GeneralPaperEqualBitDrawRates.word_bound n (k+1) b
  unfold GeneralPaperEqualBitPostprocessing.word at hw
  omega

theorem completed_height {n b : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hBudget : RationalHeight budget b)
    (p : Prepared (rounded true model W k values v hv) k budget) (trace : Trace p)
    (row : RationalResourceArray n) (hRow : (observed model A p trace).output = some row) :
    ∀ j, RationalHeight (row.allocation j) (GeneralPaperEqualBitDrawRates.word n (k+1) b) := by
  cases p with
  | dominant chosen heavy stored correct =>
    have he : (GeneralPaperEqualBitBranchDraw.copyRow A stored).1 = row := Option.some.inj hRow
    rw [← he]
    intro j
    rw [GeneralPaperEqualSelectedDraw.copy_allocation, GeneralPaperEqualBitCanonical.pure_coordinates budget chosen stored correct j]
    split_ifs
    · exact hBudget.mono (by unfold GeneralPaperEqualBitDrawRates.word GeneralPaperEqualBitDrawRates.size; omega)
    · exact (show RationalHeight (0 : ℚ) 1 by norm_num [RationalHeight]).mono
        (by unfold GeneralPaperEqualBitDrawRates.word GeneralPaperEqualBitDrawRates.size; omega)
  | grouped small sampler hK hB =>
    let p := sampler.prepared
    change (GeneralPaperEqualFullBitDraw.observed sampler.categorical model sampler.address trace).output = some row at hRow
    unfold GeneralPaperEqualFullBitDraw.observed at hRow
    rw [GeneralPaperEqualFullBitDraw.data] at hRow
    obtain ⟨slot, _hSlot, he⟩ := Option.map_eq_some_iff.mp hRow
    rw [← he]
    intro j
    have hs : 2 ≤ GeneralPaperEqualNativeSampler.segmentHeight n (k+1) := by
      unfold GeneralPaperEqualNativeSampler.segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
      omega
    have hNativeBudget : RationalHeight p.budget b := by rw [hB]; exact hBudget
    have h := GeneralPaperEqualCachedEmission.emit_height p model (fun w => w) sampler.address hs
      (GeneralPaperEqualFirstHeights.lottery_height true model W k values v hv small) hNativeBudget
      (by omega : 1 ≤ binaryWordWidth n+k+10)
      (GeneralPaperEqualFirstHeights.route_height true model W k values v hv small p) slot
      (GeneralPaperEqualRejectionTraceMeasure.scalar p.D p.midpointBits trace.1 trace.2) j
    have hk : p.midpointBits = k+5 := sampler.exponent_correct.trans (congrArg (fun k => k+5) hK)
    have hSize : expressionHeightBudget (max (binaryWordWidth n+k+10)
        (GeneralPaperEqualCachedEmission.scaledHeight (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) p.midpointBits b)) 1 ≤
        GeneralPaperEqualBitDrawRates.word n (k+1) b := by
      rw [hk]
      exact height_bound n k b
    exact h.mono hSize

theorem written_bits {n b : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hBudget : RationalHeight budget b)
    (p : Prepared (rounded true model W k values v hv) k budget) (trace : Trace p)
    (row : RationalResourceArray n) (hRow : (observed model A p trace).output = some row) :
    ∀ j, rationalWordWidth (row.allocation j) ≤ 1+2*GeneralPaperEqualBitDrawRates.word n (k+1) b :=
  fun j => rationalWordWidth_of_height (completed_height model W A k values v hv budget hBudget p trace row hRow j)

end Blotto.GeneralPaperEqualFirstBitOutput
