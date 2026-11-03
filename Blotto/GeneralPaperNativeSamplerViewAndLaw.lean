import Blotto.GeneralPaperNativeReturnedDescriptionHeadline

/-! Erased canonical views of the actual stored sampler. Repricing the
draw preserves its whole-player laws and every-output budget guarantees.
Preparation work and retained data are not recomputed by this view. -/
namespace Blotto.GeneralPaperNativeSamplerViewAndLaw
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

theorem native_view {n : ℕ} (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let actual := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ physical : GeneralPaperOriginalDrawEquilibrium.Columns t.rows o.m (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler=some (⟨o,b,GeneralPaperSamplingControls.specification _ t.rowBits k
        (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k),
        (make model.rat (fun w => w) Ap o
          (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
          (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
          (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1⟩) := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  obtain ⟨physical,hSource,_hRich,_hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model Wv Ws k values v hv b hb
  have hDescription := GeneralPaperOriginalStrategyDriver.bit_description model Wv Ws Ap k values v hv b hb physical hSource
  exact ⟨physical,GeneralPaperClosedStrategyDriver.close_some (fun w => w) Ap raw _ hDescription⟩

theorem made_law_reprice {n T K : ℕ} (bits bits' : Bool) (primitive primitive' : ℕ → ℕ) (A A' R L S : ℕ)
    (hT : T=2^R) (hS : S=2^L) (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hRep : GeneralPaperNativeReductionShape.ReplacedShape o)
    (hNo : GeneralPaperUnreplacedShape.Shape o) (hR : 0<o.representatives)
    (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (c : ℚ) (reciprocal : Bool) :
    GeneralPaperStrategyDescription.law bits primitive A R L S hT hS model o (make price index Ap o hRep hNo hR physical).1 c reciprocal=
      GeneralPaperStrategyDescription.law bits' primitive' A' R L S hT hS model o (make price index Ap o hRep hNo hR physical).1 c reciprocal := by
  by_cases hFlag : o.replaced=true
  · have hm := (hRep hFlag).1
    rw [make_circle price index Ap o hRep hNo hR physical hFlag hm]
    dsimp only
    rw [law_circle,law_circle,GeneralPaperCachedCircleSampler.law_data,GeneralPaperCachedCircleSampler.law_data,
      GeneralPaperNativeFairSamplerLaw.data,GeneralPaperNativeFairSamplerLaw.data]
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    have hm := (hNo hFalse).1
    rw [make_direct price index Ap o hRep hNo hR physical hFalse hm]
    dsimp only
    rw [law_direct,law_direct,GeneralPaperDirectRowSampler.law_data,GeneralPaperDirectRowSampler.law_data]

theorem stored_made_law_reprice {n T K : ℕ} (bits bits' : Bool) (primitive primitive' : ℕ → ℕ) (A A' R k : ℕ)
    (hT : T=2^R) (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hRep : GeneralPaperNativeReductionShape.ReplacedShape o)
    (hNo : GeneralPaperUnreplacedShape.Shape o) (hR : 0<o.representatives)
    (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (b : ℚ) (reciprocal : Bool) :
    let sampler : Sampler n T K := ⟨o,b,GeneralPaperSamplingControls.specification T R k hT,(make price index Ap o hRep hNo hR physical).1⟩
    law bits primitive A model sampler reciprocal=law bits' primitive' A' model sampler reciprocal := by
  dsimp only
  rw [law_data,law_data]
  exact made_law_reprice bits bits' primitive primitive' A A' R (k+6) (GeneralPaperNativeSelectedSecurity.count k)
    hT (GeneralPaperNativeSelectedSecurity.count_power k) model price index Ap o hRep hNo hR physical _ reciprocal


theorem made_guarantee_reprice {n T K : ℕ} (bits bits' : Bool) (primitive primitive' : ℕ → ℕ) (A A' R k : ℕ)
    (hT : T=2^R) (model : RationalCostModel) (price index : ℕ → ℕ) (Ap : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hRep : GeneralPaperNativeReductionShape.ReplacedShape o)
    (hNo : GeneralPaperUnreplacedShape.Shape o) (hR : 0<o.representatives)
    (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) (b : ℚ) (v : Values n) (B e : ℝ)
    (hG : GeneralPaperClosedStrategyEquilibrium.Guarantee bits primitive A model v B e
      (⟨o,b,GeneralPaperSamplingControls.specification T R k hT,(make price index Ap o hRep hNo hR physical).1⟩:Sampler n T K)) :
    GeneralPaperClosedStrategyEquilibrium.Guarantee bits' primitive' A' model v B e
      (⟨o,b,GeneralPaperSamplingControls.specification T R k hT,(make price index Ap o hRep hNo hR physical).1⟩:Sampler n T K) := by
  have hRich := stored_made_law_reprice bits bits' primitive primitive' A A' R k hT model price index Ap o hRep hNo hR physical b false
  have hPoor := stored_made_law_reprice bits bits' primitive primitive' A A' R k hT model price index Ap o hRep hNo hR physical b true
  apply GeneralPaperClosedStrategyEquilibrium.of_laws
  · rw [←hRich]
    exact hG.1
  · rw [←hPoor]
    exact hG.2.1
  · rw [←hRich,←hPoor]
    exact hG.2.2.1
  · rw [←hRich,←hPoor]
    exact hG.2.2.2.1

theorem native_arithmetic_draw_work {n : ℕ} (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (epsilon : ℚ) (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let actual := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    ∀ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler=some sampler →
      ∀ (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool),
        (run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤131072*(n+binaryWordWidth ⌈epsilon⁻¹⌉₊) := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  obtain ⟨physical,hNative⟩ := native_view model Wv Ws Ap words values v hv b hb
  have he : sampler=_ := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  intro reciprocal fresh
  have hWork := GeneralPaperClosedArithmeticSampling.source_sampler_work true model Wv k values v hv model.rat (fun w => w) Ap b physical reciprocal fresh
  have hExact : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent :=
    GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) Ap words epsilon hInput
  have hk : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := hExact ▸ GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  have hn := v.fields_positive
  exact hWork.trans (by nlinarith only [hk,hn])


theorem native_epsilon_at_draw_reference {n : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) :
    let actual := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    ∀ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler=some sampler → GeneralPaperClosedStrategyEquilibrium.Guarantee bits primitive A model v.values (b:ℝ) (epsilon:ℝ) sampler := by
  dsimp only
  intro sampler hSampler
  obtain ⟨other,hOther,hGuarantee⟩ := GeneralPaperClosedStrategyEquilibrium.bit_epsilon model Wv Ws Ap words epsilon hE hOne hInput values v hv b hb model.rat
  have heOther : other=sampler := Option.some.inj (hOther.symm.trans hSampler)
  subst other
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  obtain ⟨physical,hNative⟩ := native_view model Wv Ws Ap words values v hv b hb
  have he : sampler=_ := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  exact made_guarantee_reprice true bits model.rat primitive Ap A t.rowBits k
    (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k)
    model model.rat (fun w => w) Ap o
    (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values)
    physical b v.values (b:ℝ) (epsilon:ℝ) hGuarantee

end Blotto.GeneralPaperNativeSamplerViewAndLaw
