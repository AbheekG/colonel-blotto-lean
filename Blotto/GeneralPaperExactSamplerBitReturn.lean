import Blotto.GeneralPaperExactSamplerSourceBounds

/-! Actual closed original-input preparation returns inherit exact-route
source-height, full operand-price, rational-output and fresh-bit contracts.
All retained columns and controls come from the once-executed producer. -/
namespace Blotto.GeneralPaperExactSamplerBitReturn
open GeneralPaperOriginalDrawEquilibrium GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperClosedBitSampling (profile outputHeight outputBits reference bits_of_height)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem bit_return_bounds {n : ℕ} (model : RationalCostModel) (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := reference n o.m k
    ∃ sampler : Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).work≤
          profile model A (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rowBits k B H o ∧
        (∀ j,RationalHeight ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output.read j) (outputHeight o B H)) ∧
        outputBits (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output≤n*(1+2*outputHeight o B H) ∧
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*GeneralPaperExactStoredSampler.shifts sampler) := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  let A := reference n o.m k
  obtain ⟨physical,hSource,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model Wv Ws k values v hv b hb
  have hDescription := GeneralPaperOriginalStrategyDriver.bit_description model Wv Ws Ap k values v hv b hb physical hSource
  let made : Description o t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
    (make model.rat (fun w => w) Ap o (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
      (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1
  let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
    ⟨o,b,GeneralPaperSamplingControls.specification _ t.rowBits k
      (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k),made⟩
  dsimp only
  refine ⟨sampler,GeneralPaperClosedStrategyDriver.close_some (fun w => w) Ap raw made hDescription,?_⟩
  intro reciprocal fresh
  have hA : 1≤A := by unfold A reference;omega
  have hCapacity : 1+binaryWordWidth (2*n+o.representatives+2)≤A := by
    dsimp only [o]
    rw [GeneralPaperNativeReductionShape.original_representatives]
    unfold A reference
    omega
  have hRow : binaryWordWidth (t.rows+1)≤A := by unfold A reference;dsimp only [t];omega
  have h := GeneralPaperExactSamplerSourceBounds.source_sampler_bounds model Wv k Ap A B H values v hv b hB hA physical hRich hPoor hCapacity hRow reciprocal fresh
  exact ⟨h.1,h.2,bits_of_height _ _ h.2,GeneralPaperExactStoredSampler.logarithmic_bits true model.rat A model sampler reciprocal fresh⟩

end Blotto.GeneralPaperExactSamplerBitReturn
