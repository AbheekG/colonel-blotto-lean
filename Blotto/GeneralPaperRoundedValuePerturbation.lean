import Blotto.GeneralPaperValuePerturbation
import Blotto.GeneralPaperReducedErrorBudget

/-! Erased canonical observation of native rounded weights. The value
distance and regret loss are derived from the actual return, for either
paper scale. No extra rounding call is introduced into an executable driver. -/
namespace Blotto.GeneralPaperRoundedValuePerturbation
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

noncomputable def selector {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (hc : 0<c)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    RationalFieldSelector n :=
  let rounded := (GeneralPaperValueRoundingPaperContract.run bits model W c k values).1
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W c k hc values v hv
  GeneralPaperNativeRationalValues.selector rounded.2 hp.1 rounded.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W c k values)

theorem weight {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (hc : 0<c)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (j : Fin n) :
    (selector bits model W c k hc values v hv).weight j=
      ((GeneralPaperValueRoundingPaperContract.run bits model W c k values).1.1.read j:ℚ)/
        (GeneralPaperValueRoundingPaperContract.run bits model W c k values).1.2 := rfl

theorem distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (hc : 0<c)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (selector bits model W c k hc values v hv).values≤
      ((1/(2:ℝ)^k)/c)*2 := by
  have h := GeneralPaperValueRoundingPaperContract.error bits model W c k hc values v hv
  rw [GeneralPaperValueRoundingPaperContract.scaled_error c n k hc v.fields_positive] at h
  have hr : (((∑ j,|((GeneralPaperValueRoundingPaperContract.run bits model W c k values).1.1.read j:ℚ)/
      (GeneralPaperValueRoundingPaperContract.run bits model W c k values).1.2-v.weight j|):ℚ):ℝ)≤
      (((((1/(2:ℚ)^k)/c)*2):ℚ):ℝ) := by exact_mod_cast h
  rw [GeneralPaperValuePerturbation.symmetric]
  simpa only [GeneralPaperValuePerturbation.distance,RationalFieldSelector.values,
    selector,GeneralPaperNativeRationalValues.selector,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,
    Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hr

theorem original_distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (selector bits model W 256 k (by decide) values v hv).values≤
      (1/(2:ℝ)^k)/128 := by
  have h := distance bits model W 256 k (by decide) values v hv
  exact h.trans_eq (by ring)

theorem reduced_distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (selector bits model W 512 k (by decide) values v hv).values≤
      (1/(2:ℝ)^k)/256 := by
  have h := distance bits model W 512 k (by decide) values v hv
  exact h.trans_eq (by ring)

theorem original_regret {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (B : ℝ) (hB : 0≤B) (μ ν : Mixed n) :
    regret v.values B μ ν≤regret (selector bits model W 256 k (by decide) values v hv).values B μ ν+
      (1/(2:ℝ)^k)/64 := by
  have h := GeneralPaperValuePerturbation.regret_le_shift v.values
    (selector bits model W 256 k (by decide) values v hv).values B hB μ ν
  have hd := original_distance bits model W k values v hv
  linarith only [h,hd]

theorem reduced_regret {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (B : ℝ) (hB : 0≤B) (μ ν : Mixed n) :
    regret v.values B μ ν≤regret (selector bits model W 512 k (by decide) values v hv).values B μ ν+
      2*((1/(2:ℝ)^k)/256) := by
  have h := GeneralPaperValuePerturbation.regret_le_shift v.values
    (selector bits model W 512 k (by decide) values v hv).values B hB μ ν
  have hd := reduced_distance bits model W k values v hv
  linarith only [h,hd]

theorem reduced_gap (m k : ℕ) (hm : 0<m) :
    3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℝ)+(m:ℝ)/(GeneralPaperProxyParameters.prepare m k).S+
        2*((1/(2:ℝ)^k)/256)<(1/(2:ℝ)^k)/16 := by
  have h := GeneralPaperReducedErrorBudget.gap_with_values_lt m k hm
  have hr : (((3*(GeneralPaperSourceParameters.prepare k).z/32+
      2/((GeneralPaperProxyParameters.prepare m k).K:ℚ)+(m:ℚ)/(GeneralPaperProxyParameters.prepare m k).S+
        2*(GeneralPaperReducedErrorBudget.accuracy k/256)):ℚ):ℝ)<
      (((GeneralPaperReducedErrorBudget.accuracy k/16):ℚ):ℝ) := by exact_mod_cast h
  simpa only [GeneralPaperReducedErrorBudget.accuracy,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_pow,Rat.cast_one,Rat.cast_ofNat] using hr

end Blotto.GeneralPaperRoundedValuePerturbation
