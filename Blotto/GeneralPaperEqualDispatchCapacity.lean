import Blotto.GeneralPaperEqualDispatchLifetime

/-! One uniform constructed word covers all joined dispatch phases.
Numerical capacity is proved for the literal observers; allocation/reference
pricing and selected-return draw representation remain separate obligations. -/
namespace Blotto.GeneralPaperEqualDispatchCapacity
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra GeneralPaperEqualDispatchLifetime
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem grouped_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (groupedProfile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨C,hC⟩ := GeneralPaperEqualFullInitializationResources.uniform_word_growth model hFast
  refine ⟨C + 1, fun p W K => ?_⟩
  classical
  unfold groupedProfile
  split_ifs with h
  · have hg := hC (grouped p h) W K
    change binaryWordWidth _ ≤ C * (logarithm p + binaryWordWidth W + binaryWordWidth K) at hg
    nlinarith only [hg]
  · have hL := logarithm_positive p
    have hz : binaryWordWidth 0 = 1 := by decide
    rw [hz]
    nlinarith only [hL]

theorem grouped_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => groupedProfile model (word K p) K p) ledger logarithm := by
  obtain ⟨A,e,h⟩ := GeneralPaperEqualFullInitializationResources.profile_rate model hFast K
  refine ⟨A,e, fun p => ?_⟩
  classical
  dsimp only
  unfold groupedProfile
  split_ifs with small
  · exact h (grouped p small)
  · exact Nat.zero_le _

theorem parent_cap_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (parentCap model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hS := GeneralPaperEqualInputInitializerCapacity.lift_small model originalSize (GeneralPaperEqualInputDomain.original_small model)
  have hSRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => GeneralPaperValueRoundingInputPrice.inputSize a.input.values) L := hS
  have hb := GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (GeneralPaperEqualInputDomain.budget_small model)
  have hbRaw : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => rationalWordWidth a.input.budget) L := hb
  have hE := GeneralPaperEqualInputInitializerCapacity.lift_small model accuracySize (GeneralPaperEqualInputDomain.accuracy_small model)
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (GeneralPaperEqualInputDomain.count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (GeneralPaperEqualInputDomain.exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [L, GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hK : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.coefficient) L := by
    refine ⟨1, fun a => ?_⟩
    dsimp only [L, GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hBase : Tight (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => logarithm a.input) L :=
    ⟨1,fun a => by dsimp only [L, GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega⟩
  have hBaseSmall := small_of_tight hBase hL
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => parentCap model a.reference a.coefficient a.input) L := by
    unfold parentCap GeneralPaperEqualBitDispatch.bound
    simp only [GeneralPaperEqualBitPreparationRates.ledger_eq]
    dsimp only [parentCap, word, GeneralPaperEqualInputInitialization.initializationPrice,
    GeneralPaperEqualReferenceConstruction.measuredProfile, GeneralPaperValueInputWordLength.profile,
    GeneralPaperValueInputWordLength.unit, GeneralPaperWordLengthLifetime.rationalProfile,
    GeneralPaperEqualReferenceConstruction.profile, GeneralPaperEqualReferenceConstruction.cap,
    GeneralPaperBinaryAccuracyConstructionStorage.price, GeneralPaperAccuracyCountConstructionStorage.price,
    GeneralPaperAccuracyCountConstructionStorage.step, GeneralPaperAccuracyCountConstructionStorage.width,
    GeneralPaperEqualRouteConstruction.indicesWork, originalSize, budgetSize,
    GeneralPaperEqualBitDispatch.bound,
    GeneralPaperEqualBitPreparationRates.profile, GeneralPaperEqualBitPreparationRates.aggregate,
    GeneralPaperValueRoundingPaperContract.scaleBitProfile, GeneralPaperValueRoundingPaperContract.scale,
    GeneralPaperSummaryArrayExecution.arrayWord, GeneralPaperEqualLengthArray.height, expressionHeightBudget,
    GeneralPaperEqualPackingExecution.unit, GeneralPaperNatPowerOperands.width,
    GeneralPaperNaturalPrimitivePrice.binary, GeneralPaperNaturalPrimitivePrice.word,
    GeneralPaperEqualBitBranchRates.scanProfile, GeneralPaperEqualBitBoundaryScan.stepBound,
    GeneralPaperEqualBitVertex.bound, GeneralPaperEqualRouteConstruction.indicesWork]
    fun_prop (config := {maxSteps := 50000})
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem parent_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => parentProfile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model, 1 ≤ ledger p := ledger_positive
  obtain ⟨C,hC⟩ := parent_cap_word_growth model hFast
  have hm : Tight (fun p : Input model => logarithm p + binaryWordWidth (word K p) + binaryWordWidth K) logarithm := by
    have hBase : Tight (logarithm (model := model)) logarithm := ⟨1,fun _ => by omega⟩
    fun_prop
  obtain ⟨D,hD⟩ := hm
  have hc : Small (fun p : Input model => parentCap model (word K p) K p) logarithm := by
    refine ⟨C * D,fun p => ?_⟩
    exact (hC p _ K).trans ((Nat.mul_le_mul_left C (hD p)).trans_eq (by ring))
  dsimp only [parentProfile]
  fun_prop

theorem profile_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    Bound (fun p : Input model => profile model (word K p) K p) ledger logarithm := by
  have hL : ∀ p : Input model, 1 ≤ logarithm p := logarithm_positive
  have hi := GeneralPaperEqualInputInitializerCapacity.profile_rate model hFast K
  have hl := GeneralPaperEqualDispatchLocalRates.profile_rate model hFast K
  have hg := grouped_rate model hFast K
  have hp := parent_rate model hFast K
  unfold profile
  fun_prop

theorem uniform_word_growth (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ C : ℕ, ∀ (p : Input model) (W K : ℕ), binaryWordWidth (profile model W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K) := by
  obtain ⟨Ci,hi⟩ := GeneralPaperEqualInputInitializerCapacity.uniform_word_growth model hFast
  obtain ⟨Cl,hl⟩ := GeneralPaperEqualDispatchLocalRates.uniform_word_growth model hFast
  obtain ⟨Cg,hg⟩ := grouped_word_growth model hFast
  obtain ⟨Cp,hp⟩ := parent_cap_word_growth model hFast
  let L := GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure (model := model)
  have hL : ∀ a : GeneralPaperEqualInputInitializerCapacity.Parameters model, 1 ≤ L a :=
    GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hInit : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualInputInitializerLifetime.profile model a.reference a.coefficient a.input) L := ⟨Ci,fun a => hi a.input a.reference a.coefficient⟩
  have hLocal : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      GeneralPaperEqualDispatchLocalRates.profile model a.reference a.input) L := ⟨Cl,fun a => hl a.input a.reference a.coefficient⟩
  have hGrouped : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      groupedProfile model a.reference a.coefficient a.input) L := ⟨Cg,fun a => hg a.input a.reference a.coefficient⟩
  have hCap : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model =>
      parentCap model a.reference a.coefficient a.input) L := ⟨Cp,fun a => hp a.input a.reference a.coefficient⟩
  have hW : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => a.reference) L := by
    refine ⟨1,fun a => ?_⟩
    dsimp only [L, GeneralPaperEqualInputInitializerCapacity.logarithmicMeasure]; omega
  have hAll : Small (fun a : GeneralPaperEqualInputInitializerCapacity.Parameters model => profile model a.reference a.coefficient a.input) L := by
    dsimp only [profile,parentProfile]
    fun_prop
  obtain ⟨C,hC⟩ := hAll
  exact ⟨C,fun p W K => hC ⟨p,W,K⟩⟩

theorem uniform_capacity (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ p : Input model, profile model (word K p) K p < 2 ^ word K p :=
  GeneralPaperSelfReferenceCapacity.uniform_capacity (profile model) logarithm logarithm_positive (uniform_word_growth model hFast)

end Blotto.GeneralPaperEqualDispatchCapacity
