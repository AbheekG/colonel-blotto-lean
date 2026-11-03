import Blotto.GeneralPaperEqualInputRates

/-! One global model coefficient gives every unrestricted initializer phase
capacity at its actual constructed word. All envelopes are erased analysis;
execution never evaluates them to select its coefficient or reference. -/
namespace Blotto.GeneralPaperEqualInputInitializerCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

structure Parameters (model : RationalCostModel) where
  input : Input model
  reference : ℕ
  coefficient : ℕ

def logarithmicMeasure {model : RationalCostModel} (a : Parameters model) : ℕ :=
  logarithm a.input + binaryWordWidth a.reference + binaryWordWidth a.coefficient

theorem measure_positive {model : RationalCostModel} (a : Parameters model) : 1 ≤ logarithmicMeasure a := by
  have h := logarithm_positive a.input
  dsimp only [logarithmicMeasure]
  omega

theorem lift_small (model : RationalCostModel) (f : Input model → ℕ) (hf : Small f logarithm) :
    Small (fun a : Parameters model => f a.input) logarithmicMeasure := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun a => ?_⟩
  exact (hC a.input).trans (Nat.mul_le_mul_left C (by dsimp only [logarithmicMeasure]; omega))

theorem lift_tight (model : RationalCostModel) (f : Input model → ℕ) (hf : Tight f logarithm) :
    Tight (fun a : Parameters model => f a.input) logarithmicMeasure := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, fun a => ?_⟩
  exact (hC a.input).trans (Nat.mul_le_mul_left C (by dsimp only [logarithmicMeasure]; omega))

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ),
      binaryWordWidth (GeneralPaperEqualInputInitializerLifetime.profile model W K p) ≤
        C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  have hL : ∀ a : Parameters model, 1 ≤ logarithmicMeasure a := measure_positive
  have hS := lift_small model originalSize (GeneralPaperEqualInputDomain.original_small model)
  have hSRaw : Small (fun a : Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) logarithmicMeasure := hS
  have hb := lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure := hb
  have hE := lift_small model accuracySize (GeneralPaperEqualInputDomain.accuracy_small model)
  have hn := lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hW : Small (fun a : Parameters model => a.reference) logarithmicMeasure := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [logarithmicMeasure]
    omega
  have hK : Small (fun a : Parameters model => a.coefficient) logarithmicMeasure := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [logarithmicMeasure]
    omega
  have hBase : Tight (fun a : Parameters model => logarithm a.input) logarithmicMeasure :=
    ⟨1, fun a => by dsimp only [logarithmicMeasure]; omega⟩
  have hBaseSmall := small_of_tight hBase hL
  have hReturned : Small (fun a : Parameters model => word a.coefficient a.input) logarithmicMeasure := by
    unfold word
    fun_prop
  have hAll : Small (fun a : Parameters model => GeneralPaperEqualInputInitializerLifetime.profile model a.reference a.coefficient a.input)
      logarithmicMeasure := by
    dsimp only [GeneralPaperEqualInputInitializerLifetime.profile,
      GeneralPaperEqualInputInitializerLifetime.scratchProfile,
      GeneralPaperEqualInputInitializerLifetime.returnedProfile,
      GeneralPaperEqualInputInitializerLifetime.sumProfile,
      GeneralPaperEqualReferenceWordLifetime.profile,
      GeneralPaperValueInputLengthLifetime.profile,
      GeneralPaperValueInputLengthLifetime.frameProfile,
      GeneralPaperPackingAllocationLifetime.indicesProfile,
      GeneralPaperIndexedArrayLifetime.frame,
      GeneralPaperPositiveScanLifetime.labelProfile,
      GeneralPaperBinaryAccuracyConstructionStorage.profile,
      GeneralPaperBinaryAccuracyConstructionStorage.cap,
      GeneralPaperAccuracyCountConstructionStorage.profile,
      GeneralPaperAccuracyCountConstructionStorage.frameProfile,
      GeneralPaperAccuracyCountConstructionStorage.cap,
      GeneralPaperBooleanRulerWorkStorage.profile,
      GeneralPaperBooleanRulerWorkStorage.budget,
      GeneralPaperEqualInputInitializerLifetime.cursorProfile,
      GeneralPaperEqualInputInitializerLifetime.controlProfile,
      GeneralPaperEqualInputInitializerLifetime.controlCap,
      GeneralPaperEqualInputInitialization.initializationPrice,
      GeneralPaperEqualReferenceConstruction.measuredProfile,
      GeneralPaperEqualReferenceConstruction.profile,
      GeneralPaperEqualReferenceConstruction.cap,
      GeneralPaperWordLengthLifetime.rationalProfile,
      GeneralPaperValueInputWordLength.profile,
      GeneralPaperValueInputWordLength.unit,
      GeneralPaperEqualRouteConstruction.indicesWork,
      GeneralPaperBinaryAccuracyConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.step,
      GeneralPaperAccuracyCountConstructionStorage.width,
      GeneralPaperEqualInputInitializerLifetime.inputProfile,
      expressionHeightBudget]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C, hC⟩ := hAll
  exact ⟨C, fun p W K => hC ⟨p, W, K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      GeneralPaperEqualInputInitializerLifetime.profile model (word K p) K p < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (GeneralPaperEqualInputInitializerLifetime.profile model)
    logarithm logarithm_positive (uniform_word_growth model hFast)

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => GeneralPaperEqualInputInitializerLifetime.profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  have hOriginal : Bound (originalSize (model := model)) ledger logarithm := GeneralPaperEqualInputRates.value_bound model
  have hBudget : Bound (budgetSize (model := model)) ledger logarithm := GeneralPaperEqualInputRates.budget_bound model
  dsimp only [GeneralPaperEqualInputInitializerLifetime.profile,
      GeneralPaperEqualInputInitializerLifetime.scratchProfile,
      GeneralPaperEqualInputInitializerLifetime.returnedProfile,
      GeneralPaperEqualInputInitializerLifetime.sumProfile,
      GeneralPaperEqualReferenceWordLifetime.profile,
      GeneralPaperValueInputLengthLifetime.profile,
      GeneralPaperValueInputLengthLifetime.frameProfile,
      GeneralPaperPackingAllocationLifetime.indicesProfile,
      GeneralPaperIndexedArrayLifetime.frame,
      GeneralPaperPositiveScanLifetime.labelProfile,
      GeneralPaperBinaryAccuracyConstructionStorage.profile,
      GeneralPaperBinaryAccuracyConstructionStorage.cap,
      GeneralPaperAccuracyCountConstructionStorage.profile,
      GeneralPaperAccuracyCountConstructionStorage.frameProfile,
      GeneralPaperAccuracyCountConstructionStorage.cap,
      GeneralPaperBooleanRulerWorkStorage.profile,
      GeneralPaperBooleanRulerWorkStorage.budget,
      GeneralPaperEqualInputInitializerLifetime.cursorProfile,
      GeneralPaperEqualInputInitializerLifetime.controlProfile,
      GeneralPaperEqualInputInitializerLifetime.controlCap,
      GeneralPaperEqualInputInitialization.initializationPrice,
      GeneralPaperEqualReferenceConstruction.measuredProfile,
      GeneralPaperEqualReferenceConstruction.profile,
      GeneralPaperEqualReferenceConstruction.cap,
      GeneralPaperWordLengthLifetime.rationalProfile,
      GeneralPaperValueInputWordLength.profile,
      GeneralPaperValueInputWordLength.unit,
      GeneralPaperEqualRouteConstruction.indicesWork,
      GeneralPaperBinaryAccuracyConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.price,
      GeneralPaperAccuracyCountConstructionStorage.step,
      GeneralPaperAccuracyCountConstructionStorage.width,
      GeneralPaperEqualInputInitializerLifetime.inputProfile,
      expressionHeightBudget]
  fun_prop (config := {maxSteps := 50000})

theorem all_phases_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (A : ℕ) (p : Input model),
      let W := (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2
      ∀ phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n,
        GeneralPaperEqualInputInitializerLifetime.window model W K p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := uniform_capacity model hFast
  refine ⟨K, hK, fun A p phase => ?_⟩
  rw [GeneralPaperEqualInputInitialization.initialized_word]
  exact (GeneralPaperEqualInputInitializerLifetime.all_phases model _ K p phase).trans_lt (hSafe p)

end Blotto.GeneralPaperEqualInputInitializerCapacity
