import Blotto.GeneralPaperExactSamplerCounts

/-! Refined direct/circle draws of the actual numeric-real preparation
return. No accuracy encoding is traversed in this real-model entry. -/
namespace Blotto.GeneralPaperExactRealSampler
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem arithmetic_draw_work {n : ℕ} (model : RationalCostModel) (epsilon : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let prepared := (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1
    ∀ (sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet prepared.raw.strategies.original.reduced.m prepared.raw.exponent).lambda prepared.raw.exponent).rows
      (GeneralPaperProxyParameters.prepare prepared.raw.strategies.original.reduced.m prepared.raw.exponent).K),
      prepared.sampler=some sampler →
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤
          131072*(n+binaryWordWidth ⌈epsilon⁻¹⌉₊) := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  obtain ⟨physical,_pair,_hSource,_hMatches,hDescription,_hWork⟩ :=
    GeneralPaperOriginalStrategyDriver.arithmetic_return model k values v hv (b:ℝ) (by exact_mod_cast hb)
  let raw := (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
  let made : Description raw.strategies.original.reduced
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    (make (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalValueReduction.run false model 1 k values).1
      (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
      (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).1
  let canonical : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,b,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power
        (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),made⟩
  have hNative : (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1.sampler=some canonical :=
    GeneralPaperClosedStrategyDriver.close_some (fun _ => 1) 1 raw made hDescription
  have hEq : sampler=canonical := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  intro reciprocal fresh
  have hWork := GeneralPaperExactSamplerArithmetic.source_sampler_work false model 1 k values v hv (fun _ => 1) (fun _ => 1) 1 b physical reciprocal fresh
  have hk : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  have hn : 1≤n := v.fields_positive
  exact hWork.trans (by nlinarith only [hk,hn])

theorem native_controls {n : ℕ} (model : RationalCostModel) (epsilon : ℚ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    let actual := (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler = some sampler →
      sampler.controls.rows = t.rows ∧ sampler.controls.rowBits = t.rowBits ∧
      sampler.controls.shifts = GeneralPaperNativeSelectedSecurity.count k ∧
      GeneralPaperExactStoredSampler.shifts sampler =
        if o.replaced then GeneralPaperNativeSelectedSecurity.count k else 1 := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  obtain ⟨physical,_pair,_hSource,_hMatches,hDescription,_hWork⟩ :=
    GeneralPaperOriginalStrategyDriver.arithmetic_return model k values v hv (b:ℝ) (by exact_mod_cast hb)
  let raw := (GeneralPaperAccuracyStrategyDriver.arithmetic model epsilon values v hv b).1
  let made : Description raw.strategies.original.reduced
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    (make (fun _ => 1) (fun _ => 1) 1 (GeneralPaperOriginalValueReduction.run false model 1 k values).1
      (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
      (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values) physical).1
  let canonical : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K :=
    ⟨raw.strategies.original.reduced,b,GeneralPaperSamplingControls.specification _
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rowBits
      raw.exponent (GeneralPaperTrajectoryParameters.rows_power
        (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent),made⟩
  have hNative : (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1.sampler=some canonical :=
    GeneralPaperClosedStrategyDriver.close_some (fun _ => 1) 1 raw made hDescription
  have hEq : sampler=canonical := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  exact ⟨rfl, rfl, rfl, GeneralPaperExactSamplerCounts.made_shifts _ _ _ _ _ _ _ _ _ _ _ _⟩

end Blotto.GeneralPaperExactRealSampler
