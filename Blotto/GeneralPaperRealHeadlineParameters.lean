import Blotto.GeneralPaperClosedSamplerWork

/-! Original epsilon/n_* parameters for the real-RAM headline. All sizes
and logarithms here are erased analysis; the actual native accuracy choice
and reduced field count discharge their bounds without new program passes. -/
namespace Blotto.GeneralPaperRealHeadlineParameters
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def nStar (n : ℕ) (epsilon : ℚ) : ℚ := min (n:ℚ) (1/epsilon)

def timeScale (n : ℕ) (epsilon : ℚ) : ℚ := (n:ℚ)+(nStar n epsilon)^2/epsilon^5

def logarithm (n : ℕ) (epsilon : ℚ) : ℕ := 129+binaryWordWidth (n+4)+binaryWordWidth ⌈epsilon⁻¹⌉₊

theorem nstar_positive (n : ℕ) (hn : 0<n) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) : 1≤nStar n epsilon := by
  apply le_min
  · exact_mod_cast hn
  · apply (le_div_iff₀ hE).mpr
    linarith only [hOne]

theorem exponent_bound (epsilon : ℚ) :
    (GeneralPaperDyadicAccuracy.prepare epsilon).exponent≤binaryWordWidth ⌈epsilon⁻¹⌉₊ :=
  GeneralPaperDyadicAccuracy.loop_depth epsilon⁻¹ 1 (by decide)

theorem power_bound (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1) :
    (2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent≤2/epsilon := by
  have h := (GeneralPaperDyadicAccuracy.accuracy_bounds epsilon hE hOne).1
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at h
  have hp : (0:ℚ)<(2:ℚ)^(GeneralPaperDyadicAccuracy.prepare epsilon).exponent := by positivity
  have hs := (lt_div_iff₀ hp).mp h
  apply (le_div_iff₀ hE).mpr
  nlinarith only [hs]

theorem log_bound (n : ℕ) (epsilon : ℚ) :
    GeneralPaperOriginalSourceValueContract.inputLog n (GeneralPaperDyadicAccuracy.prepare epsilon).exponent 0≤logarithm n epsilon := by
  have h := exponent_bound epsilon
  have hw : binaryWordWidth (0+1)=1 := by decide
  unfold GeneralPaperOriginalSourceValueContract.inputLog logarithm
  rw [hw]
  omega

theorem logarithm_positive (n : ℕ) (epsilon : ℚ) : 1≤logarithm n epsilon := by unfold logarithm;omega

theorem structural_scale (n m k : ℕ) (hn : 0<n) (epsilon : ℚ) (hE : 0<epsilon) (hOne : epsilon<1)
    (hm : (m:ℚ)≤36*nStar n epsilon) (hPower : (2:ℚ)^k≤2/epsilon) :
    ((n+1+(m+1)^2*(2^k)^5:ℕ):ℚ)≤43808*timeScale n epsilon := by
  have hStar := nstar_positive n hn epsilon hE hOne
  have hM : (m:ℚ)+1≤37*nStar n epsilon := by linarith only [hm,hStar]
  have hM2 : ((m:ℚ)+1)^2≤(37*nStar n epsilon)^2 := by gcongr
  have hP5 : ((2:ℚ)^k)^5≤(2/epsilon)^5 := by gcongr
  have hProduct := mul_le_mul hM2 hP5 (by positivity) (by positivity)
  have hFactor : (37*nStar n epsilon)^2*(2/epsilon)^5=43808*(nStar n epsilon)^2/epsilon^5 := by ring
  rw [hFactor] at hProduct
  have hN : (1:ℚ)≤n := by exact_mod_cast hn
  push_cast
  unfold timeScale
  have hNBound : (n:ℚ)+1≤43808*(n:ℚ) := by linarith only [hN]
  have hProduct' : ((m:ℚ)+1)^2*((2:ℚ)^k)^5≤43808*((nStar n epsilon)^2/epsilon^5) :=
    hProduct.trans_eq (by ring)
  have hTotal := add_le_add hNBound hProduct'
  exact hTotal.trans_eq (by ring)

theorem original_scale {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (epsilon : ℚ)
    (hE : 0<epsilon) (hOne : epsilon<1) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) :
    let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
    let m := (GeneralPaperOriginalSourceValuePreparation.run bits model W k values v hv).1.reduced.m
    ((n+1+(m+1)^2*(2^k)^5:ℕ):ℚ)≤43808*timeScale n epsilon :=
  structural_scale n _ _ v.fields_positive epsilon hE hOne
    (GeneralPaperOriginalSourceValueContract.dyadic_field_count bits model W epsilon hE hOne values v hv) (power_bound epsilon hE hOne)

end Blotto.GeneralPaperRealHeadlineParameters
