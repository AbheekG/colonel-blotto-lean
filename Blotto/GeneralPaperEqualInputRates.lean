import Blotto.GeneralPaperEqualInputInitializerLifetime

/-! Uniform sharp preparation rates on original normalized inputs before
branch selection. All dimensions come from the actual input; initialization,
heavy scan, the selected continuation and pure budget copy are included. -/
namespace Blotto.GeneralPaperEqualInputRates
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem ledger_positive {model : RationalCostModel} (p : Input model) : 1 ≤ ledger p := by unfold ledger; omega

@[fun_prop]
theorem value_bound (model : RationalCostModel) :
    Bound (fun p : Input model => GeneralPaperValueRoundingInputPrice.inputSize p.values) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger, originalSize]; omega)

@[fun_prop]
theorem budget_bound (model : RationalCostModel) :
    Bound (fun p : Input model => rationalWordWidth p.budget) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger, budgetSize]; omega)

@[fun_prop]
theorem accuracy_bound (model : RationalCostModel) : Bound (accuracySize (model := model)) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger]; omega)

@[fun_prop]
theorem count_bound (model : RationalCostModel) : Bound (fun p : Input model => p.n) ledger logarithm :=
  pointwise _ _ _ 1 (fun p => by dsimp [ledger]; omega)

@[fun_prop]
theorem value_small (model : RationalCostModel) :
    Small (fun p : Input model => GeneralPaperValueRoundingInputPrice.inputSize p.values) logarithm :=
  GeneralPaperEqualInputDomain.original_small model

@[fun_prop]
theorem original_budget_small (model : RationalCostModel) : Small (fun p : Input model => rationalWordWidth p.budget) logarithm :=
  GeneralPaperEqualInputDomain.budget_small model

@[fun_prop]
theorem exponent_small (model : RationalCostModel) : Small (fun p : Input model => p.k) logarithm :=
  small_of_tight (exponent_tight model) logarithm_positive

@[fun_prop]
theorem exponent_polylog (model : RationalCostModel) : Polylog (fun p : Input model => p.k) logarithm :=
  polylog_of_tight (exponent_tight model)

@[fun_prop]
theorem exponent_bound (model : RationalCostModel) : Bound (fun p : Input model => p.k) ledger logarithm :=
  rate_mono (exponent_polylog model) ledger_positive

@[fun_prop]
theorem dyadic_small (model : RationalCostModel) : Small (fun p : Input model => 2 ^ p.k) logarithm :=
  power_two_small _ _ logarithm_positive (exponent_tight model)

@[fun_prop]
theorem common_word_polylog (model : RationalCostModel) (K : ℕ) :
    Polylog (GeneralPaperEqualInputDomain.word K (model := model)) logarithm :=
  polylog_of_tight (GeneralPaperEqualInputDomain.word_tight K model)

@[fun_prop]
theorem common_word_bound (model : RationalCostModel) (K : ℕ) :
    Bound (GeneralPaperEqualInputDomain.word K (model := model)) ledger logarithm :=
  rate_mono (common_word_polylog model K) ledger_positive

@[fun_prop]
theorem common_word_small (model : RationalCostModel) (K : ℕ) :
    Small (GeneralPaperEqualInputDomain.word K (model := model)) logarithm :=
  small_of_tight (GeneralPaperEqualInputDomain.word_tight K model) logarithm_positive

def bitPrice (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  let W := word K p
  GeneralPaperEqualBitDispatch.bound model W W p.k p.values p.budget

theorem bit_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (bitPrice model K) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  unfold bitPrice GeneralPaperEqualBitDispatch.bound
  simp only [GeneralPaperEqualBitPreparationRates.ledger_eq]
  dsimp only [GeneralPaperEqualBitPreparationRates.profile, GeneralPaperEqualBitPreparationRates.aggregate,
    GeneralPaperValueRoundingPaperContract.scaleBitProfile, GeneralPaperValueRoundingPaperContract.scale,
    GeneralPaperSummaryArrayExecution.arrayWord, GeneralPaperEqualLengthArray.height, expressionHeightBudget,
    GeneralPaperEqualPackingExecution.unit, GeneralPaperNatPowerOperands.width,
    GeneralPaperNaturalPrimitivePrice.binary, GeneralPaperNaturalPrimitivePrice.word,
    GeneralPaperEqualBitBranchRates.scanProfile, GeneralPaperEqualBitBoundaryScan.stepBound,
    GeneralPaperEqualBitVertex.bound, GeneralPaperEqualRouteConstruction.indicesWork]
  fun_prop (config := {maxSteps := 50000})

def sourceWork (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  let W := word K p
  (GeneralPaperEqualBitDispatch.run model W W p.k p.values p.selector p.correct p.budget).2

theorem source_work_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : sourceWork model K p ≤ bitPrice model K p :=
  GeneralPaperEqualBitDispatch.work model _ _ p.k p.values p.selector p.correct p.budget

theorem source_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (sourceWork model K) ledger logarithm := dominated (bit_price_rate model hFast K) (source_work_bound model K)

theorem initialization_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualInputInitialization.initializationPrice model
      (GeneralPaperEqualInputDomain.word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  dsimp only [GeneralPaperEqualInputInitialization.initializationPrice,
    GeneralPaperEqualReferenceConstruction.measuredProfile, GeneralPaperValueInputWordLength.profile,
    GeneralPaperValueInputWordLength.unit, GeneralPaperWordLengthLifetime.rationalProfile,
    GeneralPaperEqualReferenceConstruction.profile, GeneralPaperEqualReferenceConstruction.cap,
    GeneralPaperBinaryAccuracyConstructionStorage.price, GeneralPaperAccuracyCountConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.step, GeneralPaperAccuracyCountConstructionStorage.width,
    GeneralPaperEqualRouteConstruction.indicesWork, originalSize, budgetSize]
  fun_prop (config := {maxSteps := 50000})
def totalPrice (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitialization.initializationPrice model (word K p) K p + bitPrice model K p

def totalWork (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualInputInitialization.prepareReference model (word K p) K p).2 + sourceWork model K p

theorem total_work_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : totalWork model K p ≤ totalPrice model K p :=
  Nat.add_le_add (GeneralPaperEqualInputInitialization.initialization_work model _ K p) (source_work_bound model K p)

theorem total_price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (totalPrice model K) ledger logarithm :=
  bound_add _ _ ledger logarithm logarithm_positive (initialization_price_rate model hFast K) (bit_price_rate model hFast K)

theorem total_work_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (totalWork model K) ledger logarithm := dominated (total_price_rate model hFast K) (total_work_bound model K)

end Blotto.GeneralPaperEqualInputRates
