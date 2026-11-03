import Blotto.GeneralPaperFirstStoredWindows

/-! Resource rates hold uniformly for corrected sampler families, including
varying program coefficients. The larger measure below is erased analysis;
no per-input cost/space/capacity oracle is an executed argument. -/
namespace Blotto.GeneralPaperFirstStoredFamilies
open GeneralPaperEqualInputDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem description_rate (model : RationalCostModel) {α : Type*} (input : α → Input model) (W r L : α → ℕ)
    (sources : (x : α) → Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model (W x) (input x).k
      (input x).values (input x).selector (input x).correct) (input x).k (input x).budget)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hn : Small (fun x => (input x).n) L) (hk : Tight (fun x => (input x).k) L)
    (hb : Small (fun x => rationalWordWidth (input x).budget) L)
    (hnr : Bound (fun x => (input x).n) r L) (hbr : Bound (fun x => rationalWordWidth (input x).budget) r L) :
    Bound (fun x => GeneralPaperEqualSelectedDescription.footprint (sources x)) r L := by
  have hkSmall := small_of_tight hk hL
  have hkPoly := polylog_of_tight hk
  have hMajor : Bound (fun x => 2*GeneralPaperEqualDescriptionRates.paperBound
      (input x).n ((input x).k+1) (rationalWordWidth (input x).budget)) r L := by
    dsimp only [GeneralPaperEqualDescriptionRates.paperBound,GeneralPaperEqualNativeRetainedStorage.short,
      GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop (config := {maxSteps := 50000})
  exact dominated hMajor (fun x => GeneralPaperEqualFirstSelectedDescription.paper_bound model (W x) (input x).k
    (input x).values (input x).selector (input x).correct (input x).budget (sources x))

theorem address_tight (model : RationalCostModel) {α : Type*} (input : α → Input model) (W L : α → ℕ)
    (sources : (x : α) → Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model (W x) (input x).k
      (input x).values (input x).selector (input x).correct) (input x).k (input x).budget)
    (hL : ∀ x,1 ≤ L x) (hn : Small (fun x => (input x).n) L) (hk : Tight (fun x => (input x).k) L)
    (hb : Small (fun x => rationalWordWidth (input x).budget) L) :
    Tight (fun x => (sources x).address) L := by
  have hkSmall := small_of_tight hk hL
  have hBig : Small (fun x => (input x).n+GeneralPaperEqualBitDrawRates.word (input x).n
      (input x).k (rationalWordWidth (input x).budget)+32) L := by
    dsimp only [GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
    fun_prop
  obtain ⟨C,hC⟩ := hBig
  refine ⟨2*C+3,fun x => ?_⟩
  have h := GeneralPaperEqualSelectedSampler.address_bound (sources x)
  have hw := hC x
  have hp := hL x
  unfold GeneralPaperEqualBitDrawRates.log at h
  nlinarith only [h,hw,hp]

open GeneralPaperEqualInputInitializerCapacity (Parameters logarithmicMeasure)
open GeneralPaperUniformPreparationParameters (S M)

def source (model : RationalCostModel) (a : Parameters model) :=
  (GeneralPaperEqualFirstInputPipeline.run model 1 a.coefficient a.input).1

theorem uniform_components (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    Small (fun a : Parameters model => GeneralPaperCompleteSelectedPreparationWork.bound model (S a) (source model a)) logarithmicMeasure ∧
    Small (fun a : Parameters model => GeneralPaperSelectedOuterInputLifetime.combinedBound model (S a) (source model a)) logarithmicMeasure := by
  let r := fun a : Parameters model => ledger a.input
  have hL : ∀ a : Parameters model,1 ≤ logarithmicMeasure a := GeneralPaperEqualInputInitializerCapacity.measure_positive
  have hM : ∀ a : Parameters model,1 ≤ M a := GeneralPaperUniformPreparationParameters.scale_positive
  have hLM : ∀ a : Parameters model,logarithmicMeasure a ≤ M a := fun a => by dsimp only [M]; omega
  have hn := GeneralPaperEqualInputInitializerCapacity.lift_small model (fun p => p.n) (count_small model)
  have hk := GeneralPaperEqualInputInitializerCapacity.lift_tight model (fun p => p.k) (exponent_tight model)
  have hb : Small (fun a : Parameters model => rationalWordWidth a.input.budget) logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model budgetSize (budget_small model)
  have hr : ∀ a : Parameters model,1 ≤ r a := fun a => GeneralPaperEqualInputDomain.ledger_positive a.input
  have hrSmall : Small r logarithmicMeasure :=
    GeneralPaperEqualInputInitializerCapacity.lift_small model ledger (below_ledger_small _ (fun _ => le_rfl))
  have hnM := GeneralPaperUniformSmallComposition.small_log_mono hn hLM
  have hkM := GeneralPaperUniformSmallComposition.tight_log_mono hk hLM
  have hbM := GeneralPaperUniformSmallComposition.small_log_mono hb hLM
  have hrM := GeneralPaperUniformSmallComposition.small_log_mono hrSmall hLM
  have hNRate : Bound (fun a : Parameters model => a.input.n) r M :=
    pointwise _ _ _ 1 (fun a => by dsimp only [r,ledger]; omega)
  have hBRate : Bound (fun a : Parameters model => rationalWordWidth a.input.budget) r M :=
    pointwise _ _ _ 1 (fun a => by dsimp only [r,ledger,budgetSize]; omega)
  have hExtent := description_rate model (fun a : Parameters model => a.input) S r M (source model)
    hM hr hnM hkM hbM hNRate hBRate
  have hA := address_tight model (fun a : Parameters model => a.input) S M (source model) hM hnM hkM hbM
  have hW := GeneralPaperUniformPreparationParameters.word_tight_scale model
  have hWork := GeneralPaperCompleteSelectedPreparationWork.rate model hFast S r M
    (fun a => a.input.n) (fun a => a.input.k)
    (fun a => GeneralPaperEqualFirstNativeFacts.rounded true model (S a) a.input.k
      a.input.values a.input.selector a.input.correct) (fun a => a.input.budget) (source model) hM hr hW hA hExtent
  have hComponents := GeneralPaperSelectedPreparationGenericRates.combined_rate model hFast S r M
    (fun a => a.input.n) (fun a => a.input.k)
    (fun a => GeneralPaperEqualFirstNativeFacts.rounded true model (S a) a.input.k
      a.input.values a.input.selector a.input.correct) (fun a => a.input.budget) (source model) hM hr hW hA hExtent hrM
    (fun a => GeneralPaperEqualFirstMeasuredLayout.inner_capacity model (S a) (S a) a.input.k
      a.input.values a.input.selector a.input.correct a.input.budget (source model a))
    (fun a => by
      have h := GeneralPaperEqualFirstMeasuredLayout.total_capacity model (S a) (S a) a.input.k
        a.input.values a.input.selector a.input.correct a.input.budget (source model a)
      omega)
  exact ⟨GeneralPaperUniformSmallComposition.bound_small_scale hL hWork hrSmall
      (GeneralPaperUniformPreparationParameters.scale_small model),
    GeneralPaperUniformSmallComposition.bound_small_scale hL hComponents hrSmall
      (GeneralPaperUniformPreparationParameters.scale_small model)⟩

end Blotto.GeneralPaperFirstStoredFamilies
