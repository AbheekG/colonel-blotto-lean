import Blotto.GeneralPaperDescriptionSourceParameters

/-! Actual closed-description size in original epsilon/n_* parameters.
Original budget encoding is additive. Reference W remains explicit, so
the later global reservation proof can instantiate it without new passes. -/
namespace Blotto.GeneralPaperDescriptionHeadline
open GeneralPaperDescriptionSizeAlgebra GeneralPaperDescriptionSourceParameters
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 16384

theorem profile_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k B : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let K := (GeneralPaperProxyParameters.prepare o.m k).K
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o≤
      2^85*structural n o.m k*(word W n k)^2+2*B := by
  let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let K := (GeneralPaperProxyParameters.prepare o.m k).K
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  have hm : o.m≤n := (GeneralPaperOriginalValueReduction.count_bounds bits model Wv k values v hv).2.1
  have hw := control_words W n o.m k hm
  have hc := native_profile bits model Wv W k t.rows K H t.rowBits B values v hv hw.1 hw.2.1 hw.2.2
  have hs := shape_bound W n o.m k hm
  have h := Nat.mul_le_mul_left 8192 hs
  change GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o≤
    8192*shape n o.m t.rows K H*word W n k+2*B at hc
  change GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o≤
    2^85*structural n o.m k*(word W n k)^2+2*B
  norm_num only [Nat.reducePow] at h ⊢
  nlinarith only [hc,h,Nat.zero_le (structural n o.m k*(word W n k)^2)]

theorem bit_return_bound {n : ℕ} (model : RationalCostModel) (Wv Ws Ap W : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      GeneralPaperClosedDescriptionStorage.footprint W sampler≤4*B+2^90*structural n o.m k*(word W n k)^2 ∧
      GeneralPaperClosedDescriptionStorage.preparedFoot W prepared≤4*B+2^90*structural n o.m k*(word W n k)^2 := by
  let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let K := (GeneralPaperProxyParameters.prepare o.m k).K
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  let P := word W n k
  obtain ⟨sampler,hSampler,hBound,hPrepared⟩ := GeneralPaperClosedDescriptionStorage.bit_return_storage model Wv Ws Ap W words values v hv b hb B hB
  have hProfile := profile_bound true model Wv W k B values v hv
  change GeneralPaperClosedDescriptionStorage.footprint W sampler≤GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o at hBound
  change GeneralPaperClosedDescriptionStorage.preparedFoot W prepared≤
    2*GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o+
      arrayProfile W o.m (1+binaryWordWidth n+k+11)+(1+binaryWordWidth n+k+11)+natBits k+288*W at hPrepared
  change GeneralPaperClosedDescriptionStorage.profile W t.rows K t.rowBits k B H o≤2^85*structural n o.m k*P^2+2*B at hProfile
  have hP : 1≤P := word_positive W n k
  have hW : W≤P := by unfold P word;omega
  have hn := binaryWordWidth_mono (show n≤n+4 by omega)
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model Wv k values v hv).2.1
  change o.m≤n at hm
  have hWords : W+(1+binaryWordWidth n+k+11)≤P := by unfold P word;omega
  have hArray := Nat.mul_le_mul hm hWords
  have hKWord : natBits k≤P := by
    have h := GeneralPaperSamplingFastBitBound.word_self k
    unfold natBits P word
    omega
  have hExtra : arrayProfile W o.m (1+binaryWordWidth n+k+11)+(1+binaryWordWidth n+k+11)+natBits k+288*W≤512*(n+1)*P := by
    unfold arrayProfile
    nlinarith only [hArray,hWords,hKWord,hW,Nat.zero_le (n*P)]
  have hStructure : (n+1)*P≤structural n o.m k*P^2 := by
    apply Nat.mul_le_mul
    · unfold structural;omega
    · nlinarith only [hP]
  dsimp only
  refine ⟨sampler,hSampler,?_,?_⟩
  · change GeneralPaperClosedDescriptionStorage.footprint W sampler≤4*B+2^90*structural n o.m k*P^2
    norm_num only [Nat.reducePow] at hProfile ⊢
    nlinarith only [hBound,hProfile,Nat.zero_le (structural n o.m k*P^2)]
  · change GeneralPaperClosedDescriptionStorage.preparedFoot W prepared≤4*B+2^90*structural n o.m k*P^2
    norm_num only [Nat.reducePow] at hProfile ⊢
    nlinarith only [hPrepared,hExtra,hProfile,hStructure,Nat.zero_le (structural n o.m k*P^2)]

def epsilonWord (W n : ℕ) (epsilon : ℚ) : ℕ := 128+W+binaryWordWidth ⌈epsilon⁻¹⌉₊+binaryWordWidth (n+4)
def epsilonScale (n : ℕ) (epsilon : ℚ) : ℚ := (n:ℚ)+(GeneralPaperRealHeadlineParameters.nStar n epsilon)^2/epsilon^3

theorem epsilon_structural {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv k : ℕ) (epsilon : ℚ)
    (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (structural n (GeneralPaperOriginalValueReduction.run bits model Wv k values).1.m k:ℚ)≤10952*epsilonScale n epsilon := by
  subst k
  let m := (GeneralPaperOriginalValueReduction.run bits model Wv (GeneralPaperDyadicAccuracy.prepare epsilon).exponent values).1.m
  let N := GeneralPaperRealHeadlineParameters.nStar n epsilon
  have hStar : 1≤N := GeneralPaperRealHeadlineParameters.nstar_positive n v.fields_positive epsilon hE hOne
  have hM : (m:ℚ)≤36*N := GeneralPaperOriginalSourceValueContract.dyadic_field_count bits model Wv epsilon hE hOne values v hv
  have hPower := GeneralPaperRealHeadlineParameters.power_bound epsilon hE hOne
  have hM' : (m:ℚ)+1≤37*N := by linarith only [hM,hStar]
  have hM2 : ((m:ℚ)+1)^2≤(37*N)^2 := by gcongr
  have hP3 : ((2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)^3≤(2/epsilon)^3 := by gcongr
  have hProduct := mul_le_mul hM2 hP3 (by positivity) (by positivity)
  have hProduct' : ((m:ℚ)+1)^2*((2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)^3≤10952*(N^2/epsilon^3) :=
    hProduct.trans_eq (by ring)
  have hn : (1:ℚ)≤n := by exact_mod_cast v.fields_positive
  have hN : (n:ℚ)+1≤10952*(n:ℚ) := by linarith only [hn]
  have hTotal := add_le_add hN hProduct'
  unfold structural epsilonScale
  push_cast
  exact hTotal.trans_eq (by dsimp only [N,m];ring)

theorem epsilon_convert {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k B : ℕ) (epsilon : ℚ)
    (hE : 0<epsilon) (hOne : epsilon<1) (hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (cost : ℕ) (hCost : cost≤4*B+2^90*structural n (GeneralPaperOriginalValueReduction.run bits model Wv k values).1.m k*(word W n k)^2) :
    (cost:ℚ)≤4*(B:ℚ)+((2^90*10952:ℕ):ℚ)*epsilonScale n epsilon*(epsilonWord W n epsilon:ℚ)^2 := by
  have hScale := epsilon_structural bits model Wv k epsilon hE hOne hk values v hv
  have hK : k≤binaryWordWidth ⌈epsilon⁻¹⌉₊ := hk ▸ GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  have hWord : word W n k≤epsilonWord W n epsilon := by unfold word epsilonWord;omega
  have hPow : (word W n k:ℚ)^2≤(epsilonWord W n epsilon:ℚ)^2 := by exact_mod_cast Nat.pow_le_pow_left hWord 2
  have hPositive : 0≤epsilonScale n epsilon := by unfold epsilonScale;positivity
  have hQ : (cost:ℚ)≤4*(B:ℚ)+((2^90:ℕ):ℚ)*
      (structural n (GeneralPaperOriginalValueReduction.run bits model Wv k values).1.m k:ℚ)*(word W n k:ℚ)^2 := by exact_mod_cast hCost
  calc
    _≤4*(B:ℚ)+((2^90:ℕ):ℚ)*(structural n (GeneralPaperOriginalValueReduction.run bits model Wv k values).1.m k:ℚ)*(word W n k:ℚ)^2 := hQ
    _≤4*(B:ℚ)+((2^90:ℕ):ℚ)*(10952*epsilonScale n epsilon)*(epsilonWord W n epsilon:ℚ)^2 := by
      apply add_le_add (le_refl (4*(B:ℚ)))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hScale (by positivity)) hPow (by positivity) (by positivity)
    _=4*(B:ℚ)+((2^90*10952:ℕ):ℚ)*epsilonScale n epsilon*(epsilonWord W n epsilon:ℚ)^2 := by push_cast;ring

theorem epsilon_description {n : ℕ} (model : RationalCostModel) (Wv Ws Ap W : ℕ) (words : BinaryAccuracyWords)
    (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) (hInput : epsilon=(words.numerator.value:ℚ)/words.denominator.value)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ sampler : GeneralPaperStoredStrategySampler.Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧
      (GeneralPaperClosedDescriptionStorage.footprint W sampler:ℚ)≤4*(B:ℚ)+((2^90*10952:ℕ):ℚ)*epsilonScale n epsilon*(epsilonWord W n epsilon:ℚ)^2 ∧
      (GeneralPaperClosedDescriptionStorage.preparedFoot W prepared:ℚ)≤4*(B:ℚ)+((2^90*10952:ℕ):ℚ)*epsilonScale n epsilon*(epsilonWord W n epsilon:ℚ)^2 := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  have hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent :=
    GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) Ap words epsilon hInput
  obtain ⟨sampler,hSampler,hBound,hPrepared⟩ := bit_return_bound model Wv Ws Ap W words values v hv b hb B hB
  dsimp only
  exact ⟨sampler,hSampler,epsilon_convert true model Wv W k B epsilon hE hOne hk values v hv _ hBound,
    epsilon_convert true model Wv W k B epsilon hE hOne hk values v hv _ hPrepared⟩


@[fun_prop]
theorem profile_scaling {n : ℕ} (T K Rb k B H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperClosedDescriptionStorage.profile W T K Rb k B H o) := by
  unfold GeneralPaperClosedDescriptionStorage.profile GeneralPaperClosedDescriptionStorage.descriptionProfile
    GeneralPaperCachedCircleRetainedStorage.commonProfile GeneralPaperEnclosingSourceOwners.columnsProfile
    GeneralPaperEnclosingSourceOwners.columnProfile GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile
    GeneralPaperClosedDescriptionStorage.controlsProfile fields arrayProfile
  fun_prop

def returnProfile {n : ℕ} (W T K Rb k B H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  2*GeneralPaperClosedDescriptionStorage.profile W T K Rb k B H o+
    arrayProfile W o.m (1+binaryWordWidth n+k+11)+(1+binaryWordWidth n+k+11)+natBits k+288*W

@[fun_prop]
theorem return_profile_scaling {n : ℕ} (T K Rb k B H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => returnProfile W T K Rb k B H o) := by
  unfold returnProfile arrayProfile
  fun_prop

end Blotto.GeneralPaperDescriptionHeadline
