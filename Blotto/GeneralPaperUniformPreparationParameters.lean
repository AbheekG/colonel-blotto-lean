import Blotto.GeneralPaperSelectedPreparationGenericRates

/-! Uniform parameter domain for the canonical stored preparation. Both
the input and preparation coefficient vary. The enlarged rate scale is
used only in erased analysis, never to choose the executed reference word. -/
namespace Blotto.GeneralPaperUniformPreparationParameters
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformSmallComposition
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def S {model : RationalCostModel} (a : Parameters model) : ℕ := word a.coefficient a.input
def M {model : RationalCostModel} (a : Parameters model) : ℕ := logarithmicMeasure a + S a
def source (model : RationalCostModel) (a : Parameters model) :=
  (GeneralPaperEqualCopiedPipeline.run model (S a) a.coefficient a.input).1

theorem base_tight (model : RationalCostModel) : Tight (fun a : Parameters model => logarithm a.input) logarithmicMeasure :=
  ⟨1,fun a => by dsimp only [logarithmicMeasure]; omega⟩

theorem coefficient_small (model : RationalCostModel) : Small (fun a : Parameters model => a.coefficient) logarithmicMeasure :=
  ⟨1,fun a => by dsimp only [logarithmicMeasure]; omega⟩

theorem word_small (model : RationalCostModel) : Small (S (model := model)) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hK := coefficient_small model
  have hBase := small_of_tight (base_tight model) hL
  unfold S word
  fun_prop

theorem scale_small (model : RationalCostModel) : Small (M (model := model)) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hBase : Tight (logarithmicMeasure (model := model)) logarithmicMeasure := ⟨1,fun _ => by omega⟩
  exact small_add _ _ _ (small_of_tight hBase hL) (word_small model)

theorem scale_positive {model : RationalCostModel} (a : Parameters model) : 1 ≤ M a :=
  (GeneralPaperEqualInputInitializerCapacity.measure_positive a).trans (Nat.le_add_right _ _)

theorem word_tight_scale (model : RationalCostModel) : Tight (S (model := model)) M :=
  ⟨1,fun a => by dsimp only [M]; omega⟩

theorem native_address_tight (model : RationalCostModel) :
    Tight (fun a : Parameters model => (source model a).address) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hb : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (budget_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hBig : Small (fun a : Parameters model => a.input.n +
      GeneralPaperEqualBitDrawRates.word a.input.n a.input.k (rationalWordWidth a.input.budget) + 32) logarithmicMeasure := by
    dsimp only [GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop
  obtain ⟨C,hC⟩ := hBig
  refine ⟨2 * C + 3,fun a => ?_⟩
  have h := GeneralPaperEqualSelectedSampler.address_bound (source model a)
  have hw := hC a
  have hp := hL a
  unfold GeneralPaperEqualBitDrawRates.log at h
  nlinarith only [h,hw,hp]

theorem description_small (model : RationalCostModel) :
    Small (fun a : Parameters model => GeneralPaperEqualSelectedDescription.footprint (source model a)) logarithmicMeasure := by
  have hL := GeneralPaperEqualInputInitializerCapacity.measure_positive (model := model)
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hb : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (budget_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hkSmall := small_of_tight hk hL
  have hMajor : Small (fun a : Parameters model => 2 * GeneralPaperEqualDescriptionRates.paperBound
      a.input.n a.input.k (rationalWordWidth a.input.budget)) logarithmicMeasure := by
    dsimp only [GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  exact small_mono hMajor (fun a => GeneralPaperEqualSelectedDescription.paper_bound model (S a) a.input.k
    a.input.values a.input.selector a.input.correct a.input.budget (source model a))

theorem lift_uniform (model : RationalCostModel) (f : ℕ → ℕ → Input model → ℕ)
    (hf : ∃ C : ℕ,∀ (p : Input model) (W K : ℕ),binaryWordWidth (f W K p) ≤
      C * (logarithm p + binaryWordWidth W + binaryWordWidth K)) :
    Small (fun a : Parameters model => f (S a) a.coefficient a.input) logarithmicMeasure := by
  obtain ⟨C,hC⟩ := hf
  have hBase := base_tight model
  have hS := word_small model
  have hK := coefficient_small model
  have hMeasure : Tight (fun a : Parameters model => logarithm a.input + binaryWordWidth (S a) +
      binaryWordWidth a.coefficient) logarithmicMeasure := by
    exact tight_add _ _ _ (tight_add _ _ _ hBase hS) hK
  obtain ⟨D,hD⟩ := hMeasure
  refine ⟨C * D,fun a => ?_⟩
  exact (hC a.input (S a) a.coefficient).trans ((Nat.mul_le_mul_left C (hD a)).trans_eq (by ring))

end Blotto.GeneralPaperUniformPreparationParameters
