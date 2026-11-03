import Blotto.GeneralPaperNativeCircleSecurity

/-! Every label of a uniform whole-row law has positive probability.
Almost-sure hard support therefore certifies every labelled source row. -/
namespace Blotto.GeneralPaperUniformRowSupport
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem rows_feasible {n T : ℕ} (hT : 0<T) (rows : Fin T → Allocation n) (B : ℝ)
    (h : Supported B (GeneralPaperUniformRowLaw.law hT rows)) : ∀ r,Feasible B (rows r) := by
  change ∀ᵐ x ∂Measure.sum (fun r:Fin T => ENNReal.ofReal (1/(T:ℝ)) • Measure.dirac (rows r)),Feasible B x at h
  have ha := Measure.ae_sum_iff.mp h
  intro r
  have hc : ENNReal.ofReal (1/(T:ℝ))≠0 := by positivity
  have hr := (Measure.ae_ennreal_smul_measure_iff hc).mp (ha r)
  rw [ae_dirac_eq] at hr
  exact hr

theorem native_lift_supported {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (hT : 0<T) (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m)
    (B : ℝ) (h : Supported B (GeneralPaperUniformRowLaw.law hT rows)) :
    Supported B (GeneralPaperNativeCircleSecurity.lifted bits model W k input v hv hReplace hm hT rows) :=
  GeneralPaperNativeCircleSecurity.supported bits model W k input v hv hReplace hm hT rows B (rows_feasible hT rows B h)

end Blotto.GeneralPaperUniformRowSupport
