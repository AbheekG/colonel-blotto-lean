import Blotto.GeneralPaperExactSamplerArithmetic

/-! Native epsilon headlines for the exact stored sampler, at the actual
compact local draw reference and original input/budget precision. -/
namespace Blotto.GeneralPaperExactSamplerNativeHeadlines
open GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open GeneralPaperNativeSamplingParameters (scale logarithm)
open GeneralPaperSamplingFastBitBound (coefficient native_profile epsilon_scale epsilonLog)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem bit_return_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    {n : ℕ} (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    let A := GeneralPaperClosedBitSampling.reference n o.m k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).work≤
          coefficient C d*n*(B+scale o.m k+1)*(logarithm n k B)^(d+2) ∧
        (∀ j,RationalHeight ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output.read j)
          (GeneralPaperClosedBitSampling.outputHeight o B H)) ∧
        GeneralPaperClosedBitSampling.outputBits (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).output≤
          n*(1+2*GeneralPaperClosedBitSampling.outputHeight o B H) ∧
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*GeneralPaperExactStoredSampler.shifts sampler) := by
  obtain ⟨sampler,hSampler,hBounds⟩ := GeneralPaperExactSamplerBitReturn.bit_return_bounds model Wv Ws Ap words values v hv b hb B hB
  dsimp only
  refine ⟨sampler,hSampler,?_⟩
  intro reciprocal fresh
  have h := hBounds reciprocal fresh
  exact ⟨h.1.trans (native_profile hg Wv _ B values v hv),h.2⟩

theorem epsilon_bit_draw {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    {n : ℕ} (Wv Ws Ap : ℕ) (words : BinaryAccuracyWords) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let A := GeneralPaperClosedBitSampling.reference n o.m k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows
      (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        ((GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).work:ℚ)≤
          ((76*coefficient C d:ℕ):ℚ)*(n:ℚ)*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon)*
            (epsilonLog n epsilon B:ℚ)^(d+2) ∧
        (GeneralPaperExactStoredSampler.run true model.rat A model sampler reciprocal fresh).freshReads=
          Nat.log2 (sampler.controls.rows*GeneralPaperExactStoredSampler.shifts sampler) := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let m := (GeneralPaperOriginalValueReduction.run true model Wv k values).1.m
  have hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent :=
    GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) Ap words epsilon hInput
  have hScale := epsilon_scale model Wv k B epsilon hE hOne hk values v hv
  have hLog : logarithm n k B≤epsilonLog n epsilon B := by
    have hK : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := hk ▸ GeneralPaperRealHeadlineParameters.exponent_bound epsilon
    unfold logarithm epsilonLog
    omega
  have hPow : (logarithm n k B:ℚ)^(d+2)≤(epsilonLog n epsilon B:ℚ)^(d+2) := by
    exact_mod_cast Nat.pow_le_pow_left hLog (d+2)
  have hStar := GeneralPaperRealHeadlineParameters.nstar_positive n v.fields_positive epsilon hE hOne
  have hNonneg : (0:ℚ)≤GeneralPaperRealHeadlineParameters.nStar n epsilon := by linarith only [hStar]
  obtain ⟨sampler,hSampler,hBounds⟩ := bit_return_rate hg Wv Ws Ap words values v hv b hb B hB
  dsimp only
  refine ⟨sampler,hSampler,?_⟩
  intro reciprocal fresh
  have h := hBounds reciprocal fresh
  refine ⟨?_,h.2.2.2⟩
  have hQ : ((GeneralPaperExactStoredSampler.run true model.rat
      (GeneralPaperClosedBitSampling.reference n m k) model sampler reciprocal fresh).work:ℚ)≤
      (coefficient C d:ℚ)*(n:ℚ)*((B+scale m k+1:ℕ):ℚ)*(logarithm n k B:ℚ)^(d+2) := by exact_mod_cast h.1
  calc
    _≤(coefficient C d:ℚ)*(n:ℚ)*((B+scale m k+1:ℕ):ℚ)*(logarithm n k B:ℚ)^(d+2) := hQ
    _≤(coefficient C d:ℚ)*(n:ℚ)*(76*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon))*
        (epsilonLog n epsilon B:ℚ)^(d+2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hScale (by positivity)) hPow (by positivity) (by positivity)
    _=((76*coefficient C d:ℕ):ℚ)*(n:ℚ)*((B:ℚ)+GeneralPaperRealHeadlineParameters.nStar n epsilon/epsilon)*
        (epsilonLog n epsilon B:ℚ)^(d+2) := by push_cast;ring

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
      ∀ (reciprocal : Bool) (fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool),
        (GeneralPaperExactStoredSampler.run false (fun _ => 1) 1 model sampler reciprocal fresh).work≤131072*(n+binaryWordWidth ⌈epsilon⁻¹⌉₊) := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  obtain ⟨physical,hNative⟩ := GeneralPaperNativeSamplerViewAndLaw.native_view model Wv Ws Ap words values v hv b hb
  have he : sampler=_ := Option.some.inj (hSampler.symm.trans hNative)
  subst sampler
  intro reciprocal fresh
  have hWork := GeneralPaperExactSamplerArithmetic.source_sampler_work true model Wv k values v hv model.rat (fun w => w) Ap b physical reciprocal fresh
  have hExact : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent :=
    GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) Ap words epsilon hInput
  have hk : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := hExact ▸ GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  have hn := v.fields_positive
  exact hWork.trans (by nlinarith only [hk,hn])

end Blotto.GeneralPaperExactSamplerNativeHeadlines
