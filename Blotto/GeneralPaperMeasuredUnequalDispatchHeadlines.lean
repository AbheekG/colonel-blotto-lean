import Blotto.GeneralPaperMeasuredUnequalTime

/-! Sharp unequal headlines on the actual shared dispatcher, including its
executed branch test. The one-field branch is covered separately. -/
namespace Blotto.GeneralPaperMeasuredUnequalDispatchHeadlines
open GeneralPaperNativeResourceDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperNativeSourceTimeRates (rate rate_positive)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon paperLog log_comparison)
open GeneralPaperNativeSourceTimeHeadline (timeScale structural_scale)
open GeneralPaperAllBranchBitDispatch (branchPrice)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

noncomputable def price (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (K : ℕ) (p : Problem) : ℕ :=
  GeneralPaperMeasuredUnequalTime.price model C d cal K p + branchPrice model (GeneralPaperMeasuredReferenceGrowth.original p)

theorem price_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K) :
    Bound (price model C d cal K) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hPrep := GeneralPaperMeasuredUnequalTime.price_rate hg cal K hK
  have hBudget : Bound (fun p : Problem => rationalWordWidth p.budget) (rate model) (logarithm model) :=
    pointwise _ _ _ 1 (fun p => by unfold rate ledger originalInputSize; omega)
  have hBudgetSmall : Small (fun p : Problem => rationalWordWidth p.budget) (logarithm model) :=
    small_below_ledger model _ (fun p => by unfold ledger originalInputSize; omega)
  have hn := count_small model
  have hFast : GeneralPaperFastRationalModel.IsFast model := ⟨C, d, hg⟩
  change Bound (fun p => GeneralPaperMeasuredUnequalTime.price model C d cal K p +
    (model.rat (rationalWordWidth p.budget + 3) + 64 * (binaryWordWidth p.n + 1))) (rate model) (logarithm model)
  fun_prop (config := {maxSteps := 5000})

theorem work_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) (hN : p.n ≠ 1) :
    (GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 ≤
      price model C d cal K p := by
  rw [GeneralPaperMeasuredBitDispatch.on_unequal model K (GeneralPaperMeasuredReferenceGrowth.original p)
    hN (ne_of_lt p.budget_valid.2)]
  exact Nat.add_le_add_right (GeneralPaperMeasuredUnequalTime.work_bound hg cal K hWord p) _

theorem time_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ A e : ℕ,∀ p : Problem,p.n ≠ 1 → epsilon p<1 →
      ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := price_rate hg cal K hK
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hN hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := ((work_bound hg cal K hWord p hN).trans (hA p)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring


def DescriptionBound (_model : RationalCostModel) (W A : ℕ) (p : Problem)
    (returned : GeneralPaperClosedStrategyDriver.Prepared p.n) : Prop :=
  let o := returned.raw.strategies.original.reduced
  let k := returned.raw.exponent
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  ∃ sampler : GeneralPaperStoredStrategySampler.Sampler p.n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
    returned.sampler = some sampler ∧
    (GeneralPaperClosedDescriptionStorage.footprint W sampler : ℚ) ≤
      (A : ℚ) * GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale p * (paperLog p : ℚ) ^ 2 ∧
    (GeneralPaperClosedDescriptionStorage.preparedFoot W returned : ℚ) ≤
      (A : ℚ) * GeneralPaperNativeReturnedDescriptionHeadline.descriptionScale p * (paperLog p : ℚ) ^ 2

theorem same_return_headlines {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ At et Ad : ℕ, ∀ p : Problem, p.n ≠ 1 → epsilon p < 1 →
      ∃ output : GeneralPaperClosedStrategyDriver.Prepared p.n,
        (GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).1 =
          some (.unequal output) ∧
        ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
          (At : ℚ) * timeScale p * (paperLog p : ℚ) ^ et ∧
        GeneralPaperArbitraryPreparationDraw.Contract model C d p output ∧
        DescriptionBound model (cal.word p) Ad p output := by
  obtain ⟨At, et, hTime⟩ := time_headline hg cal K hK hWord
  obtain ⟨Ad, hDescription⟩ := GeneralPaperMeasuredUnequalSampling.description_headline K cal hWord
  refine ⟨At, et, Ad, fun p hN hOne => ?_⟩
  refine ⟨GeneralPaperMeasuredUnequalSampling.actual model K p, ?_, hTime p hN hOne,
    GeneralPaperMeasuredUnequalSampling.draw_contract hg K p hOne, hDescription p hOne⟩
  rw [GeneralPaperMeasuredBitDispatch.on_unequal model K (GeneralPaperMeasuredReferenceGrowth.original p)
    hN (ne_of_lt p.budget_valid.2)]
  rfl

theorem uniformly_calibrated {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧
      (∀ p : GeneralPaperOriginalGameInput.Input,
        GeneralPaperStoredPreparationUniformCapacity.envelope model K
          (GeneralPaperOriginalGameInput.equalInput model p) <
            2 ^ (K * GeneralPaperOriginalReferenceComparison.logarithm model p)) ∧
      ∃ At et Ad : ℕ, ∀ p : Problem, p.n ≠ 1 → epsilon p < 1 →
        ∃ output : GeneralPaperClosedStrategyDriver.Prepared p.n,
          (GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).1 =
            some (.unequal output) ∧
          ((GeneralPaperMeasuredBitDispatch.run model K (GeneralPaperMeasuredReferenceGrowth.original p)).2 : ℚ) ≤
            (At : ℚ) * timeScale p * (paperLog p : ℚ) ^ et ∧
          GeneralPaperArbitraryPreparationDraw.Contract model C d p output ∧
          GeneralPaperArbitraryPreparationDraw.Independent model p output ∧
          DescriptionBound model (GeneralPaperMeasuredReferenceGrowth.word model K p) Ad p output := by
  obtain ⟨K, hK, cal, hWord, hEqual⟩ := GeneralPaperEnlargedReferenceHeadlines.measured_calibration hg
  obtain ⟨At, et, Ad, hAll⟩ := same_return_headlines hg cal K hK hWord
  refine ⟨K, hK, hEqual, At, et, Ad, fun p hN hOne => ?_⟩
  obtain ⟨output, hReturn, hTime, hDraw, hDescription⟩ := hAll p hN hOne
  refine ⟨output, hReturn, hTime, hDraw,
    GeneralPaperArbitraryPreparationDraw.independent_of_draw p output hDraw, ?_⟩
  rw [hWord] at hDescription
  exact hDescription

end Blotto.GeneralPaperMeasuredUnequalDispatchHeadlines
