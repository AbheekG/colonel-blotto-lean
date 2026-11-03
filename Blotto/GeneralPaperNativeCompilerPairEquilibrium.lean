import Blotto.GeneralPaperSourceCompilerPairStorage
import Blotto.GeneralPaperNativeFairSamplerLaw

/-! Actual native pair return, positive rounded values, original-field
finite circle evaluation and exact fresh-bit laws join to the canonical
continuous game. Matching is derived from the stored returned arrays.
This semantic join does not discharge the remaining global driver prices,
input accuracy decoder, identity/equal-budget/one-field boundary joins. -/
namespace Blotto.GeneralPaperNativeCompilerPairEquilibrium
open GeneralPaperOriginalDrawEquilibrium GeneralPaperOriginalCirclePreparation
open GeneralPaperNativeSelectedSecurity
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

noncomputable def rounded {m : ℕ} (valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) :=
  let rounded := GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity valueBits model Wv 512 k (by decide) values v hv
  let pair := GeneralPaperSourceCompilerPairStorage.run model W k rounded.1.2 hp.1 rounded.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum valueBits model Wv 512 k values) b
  (pair.1,rounded.2+pair.2+64*W)

theorem rounded_return {m : ℕ} (valueBits : Bool) (model : RationalCostModel) (W Wv k : ℕ)
    (values : FixedArrayTable m ℚ) (v : RationalFieldSelector m) (hv : ∀ j,values.read j=v.weight j)
    (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ physical pair,(rounded valueBits model W Wv k values v hv b).1=some physical ∧
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k values v hv b=some pair ∧ Matches physical pair := by
  let weights := GeneralPaperValueRoundingPaperContract.run valueBits model Wv 512 k values
  have hp := GeneralPaperValueRoundingPaperContract.positivity valueBits model Wv 512 k (by decide) values v hv
  obtain ⟨physical,pair,hNative,hSource,hMatches,_⟩ := GeneralPaperSourceCompilerPairStorage.actual_return model W k weights.1.2 hp.1 weights.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum valueBits model Wv 512 k values) b v.fields_positive hb
  exact ⟨physical,pair,hNative,hSource,hMatches⟩

theorem original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv Wc k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let hT := GeneralPaperTrajectoryParameters.rows_positive (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ physical pair,
      (rounded valueBits model Wc Wv k o.values redValues (fun _ => rfl) (b:ℝ)).1=some physical ∧
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
      Matches physical pair ∧
        let μ := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR 1 (run price index A o hm physical.rich).1
        let ν := GeneralPaperOriginalDrawLaw.law hT (count_positive k) model o hR b (run price index A o hm physical.poor).1
        Supported 1 μ ∧ Supported (b:ℝ) ν ∧
          security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
          regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
          regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  have hbReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  obtain ⟨hm,pair,hSource,hEquilibrium⟩ := GeneralPaperOriginalDrawEquilibrium.original bits valueBits model W Wv k input v hv b hb price index A hReplace
  let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
  let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
  obtain ⟨physical,actualPair,hNative,hActual,hMatch⟩ := rounded_return valueBits model Wc Wv k o.values redValues (fun _ => rfl) (b:ℝ) hbReal
  have he : actualPair=pair := Option.some.inj (hActual.symm.trans hSource)
  subst actualPair
  exact ⟨hm,physical,pair,hNative,hSource,hMatch,hEquilibrium physical hMatch⟩

theorem sampled_original {n : ℕ} (bits valueBits : Bool) (model : RationalCostModel) (W Wv Wc k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (price index primitive : ℕ → ℕ) (A : ℕ)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    let redValues := GeneralPaperOriginalValueReduction.selector bits model W k input v hv
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    let hR := GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input
    ∃ (hm:o.m=o.classified.heavy.size+o.representatives), ∃ physical pair,
      (rounded valueBits model Wc Wv k o.values redValues (fun _ => rfl) (b:ℝ)).1=some physical ∧
      GeneralPaperRoundedValueCanonical.run valueBits model Wv k o.values redValues (fun _ => rfl) (b:ℝ)=some pair ∧
      Matches physical pair ∧
        let μ := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR 1 (run price index A o hm physical.rich).1
        let ν := GeneralPaperNativeFairSamplerLaw.law primitive A trajectory.rowBits (k+6) trajectory.rows (count k) hRows hShift model o hR b (run price index A o hm physical.poor).1
        Supported 1 μ ∧ Supported (b:ℝ) ν ∧
          security v.values 1 ν+security v.values (b:ℝ) μ<1+179*(1/(2:ℝ)^k)/320 ∧
          regret v.values 1 μ ν≤179*(1/(2:ℝ)^k)/320 ∧
          regret v.values (b:ℝ) ν μ≤179*(1/(2:ℝ)^k)/320 := by
  obtain ⟨hm,physical,pair,hNative,hSource,hMatch,hA,hB,hSecurity,hRich,hPoor⟩ :=
    original bits valueBits model W Wv Wc k input v hv b hb price index A hReplace
  dsimp only
  refine ⟨hm,physical,pair,hNative,hSource,hMatch,?_⟩
  rw [GeneralPaperNativeFairSamplerLaw.data,GeneralPaperNativeFairSamplerLaw.data]
  exact ⟨hA,hB,hSecurity,hRich,hPoor⟩

end Blotto.GeneralPaperNativeCompilerPairEquilibrium
