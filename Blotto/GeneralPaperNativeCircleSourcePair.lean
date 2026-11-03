import Blotto.GeneralPaperUniformRowSupport

/-! The actual selected source/compiler pair, lifted to the original named
fields and original input values, has canonical continuous Nash guarantees
for the full-cell mathematical reconstruction. This does not yet assert
the selected-shift sampler or complete native driver/cost/output contracts. -/
namespace Blotto.GeneralPaperNativeCircleSourcePair
open GeneralPaperNativeReductionShape GeneralPaperNativeCircleSecurity
open GeneralPaperDictionary
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem original_distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (firstSelector bits model W k input v hv).values≤(1/(2:ℝ)^k)/128 := by
  have h := GeneralPaperReducedInputContract.retained_original_error bits model W k input v hv
  have hr : (((∑ j,|((GeneralPaperOriginalValueReduction.run bits model W k input).1.firstWeights.read j:ℚ)/
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.denominator-v.weight j|):ℚ):ℝ)≤
      (((1/(2:ℚ)^k)/128:ℚ):ℝ) := by exact_mod_cast h
  rw [GeneralPaperValuePerturbation.symmetric]
  simpa only [GeneralPaperValuePerturbation.distance,firstSelector,GeneralPaperNativeRationalValues.selector,
    RationalFieldSelector.values,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,
    Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hr

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ pair,
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) b=some pair ∧
      let μ := lifted bits model W k input v hv hReplace hm hT (law pair.rich hT).realRow
      let ν := lifted bits model W k input v hv hReplace hm hT
        (fun r => scaleAllocation b ((law pair.poor hT).realRow r))
      Supported 1 μ ∧ Supported b ν ∧
        security v.values 1 ν+security v.values b μ<1+169*(1/(2:ℝ)^k)/320 ∧
        regret v.values 1 μ ν≤169*(1/(2:ℝ)^k)/320 ∧
        regret v.values b ν μ≤169*(1/(2:ℝ)^k)/320 := by
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
  let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  obtain ⟨hm,hLift⟩ := GeneralPaperNativeCircleSecurity.original bits model W k input v hv hReplace
  obtain ⟨pair,hRun,hRich,hPoor,hSec,_⟩ := GeneralPaperReducedInputContract.run_security bits valueBits model W Wv k input v hv b hb
  dsimp only
  refine ⟨hm,pair,hRun,?_⟩
  let μ := lifted bits model W k input v hv hReplace hm hT (law pair.rich hT).realRow
  let ν := lifted bits model W k input v hv hReplace hm hT (fun r => scaleAllocation b ((law pair.poor hT).realRow r))
  have hA : Supported 1 μ := by
    apply GeneralPaperUniformRowSupport.native_lift_supported
    rw [←GeneralPaperDictionaryUniformLaw.rich pair hT]
    exact hRich
  have hB : Supported b ν := by
    apply GeneralPaperUniformRowSupport.native_lift_supported
    rw [←GeneralPaperDictionaryUniformLaw.poor pair hT b]
    exact hPoor
  have hSA := hLift _ hT (law pair.rich hT).realRow b hb.1.le
  rw [←GeneralPaperDictionaryUniformLaw.rich pair hT] at hSA
  have hSB := hLift _ hT (fun r => scaleAllocation b ((law pair.poor hT).realRow r)) 1 (by norm_num)
  rw [←GeneralPaperDictionaryUniformLaw.poor pair hT b] at hSB
  have hVA := GeneralPaperValuePerturbation.security_le_shift v.values
    (firstSelector bits model W k input v hv).values b hb.1.le μ
  have hVB := GeneralPaperValuePerturbation.security_le_shift v.values
    (firstSelector bits model W k input v hv).values 1 (by norm_num) ν
  have hd := original_distance bits model W k input v hv
  have hTotal : security v.values 1 ν+security v.values b μ<1+169*(1/(2:ℝ)^k)/320 := by
    linarith only [hSec,hSA,hSB,hVA,hVB,hd]
  have hRegret := regrets_le_of_security_sum v.values μ ν hA hB hTotal.le
  exact ⟨hA,hB,hTotal,hRegret⟩

end Blotto.GeneralPaperNativeCircleSourcePair
