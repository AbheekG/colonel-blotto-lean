import Blotto.GeneralPaperOriginalDrawLaw

/-! Scaling the native unit-row output is the same whole law as scaling
the selected source rows before reconstruction. This joins the original
poor budget while retaining short unit rows throughout preparation. -/
namespace Blotto.GeneralPaperOriginalDrawScale
open MeasureTheory GeneralPaperOriginalCirclePreparation
set_option autoImplicit false
set_option maxHeartbeats 2600000

theorem one {n : ℕ} (μ : Mixed n) : scaleLaw 1 μ=μ := by
  apply ProbabilityMeasure.toMeasure_injective
  have h : scaleAllocation (1:ℝ)=(id : Allocation n → Allocation n) := by
    funext x j
    simp only [scaleAllocation,one_mul,id_eq]
  change Measure.map (scaleAllocation 1) (μ:Measure (Allocation n))=(μ:Measure (Allocation n))
  rw [h,Measure.map_id]

theorem lifted {n T : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (S : ℕ) (hS : 0<S) (hT : 0<T)
    (rows : Fin T → Allocation (GeneralPaperOriginalValueReduction.run bits model W k input).1.m) (c : ℝ) (hc : 0<c) :
    scaleLaw c (GeneralPaperNativeSelectedSecurity.lifted bits model W k input v hv hReplace hm S hS hT rows)=
      GeneralPaperNativeSelectedSecurity.lifted bits model W k input v hv hReplace hm S hS hT (fun r => scaleAllocation c (rows r)) := by
  unfold GeneralPaperNativeSelectedSecurity.lifted
  dsimp only
  rw [← GeneralPaperUniformLawMap.relabel_scale,
    GeneralPaperUniformLawMap.selected_scale _ _ S _ _ hS hT _ _ c hc]
  rfl

theorem native_scaled {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hS : 0<S) (price index : ℕ → ℕ) (A : ℕ) (c : ℚ) (hc : 0<c) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    GeneralPaperOriginalDrawLaw.law hT hS model o (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input) c
      (run price index A o hm columns).1=
      GeneralPaperNativeSelectedSecurity.lifted bits model W k input v hv hReplace hm S hS hT
        (fun r => scaleAllocation (c:ℝ) ((GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow r)) :=
  (GeneralPaperOriginalDrawLaw.original bits model W k input v hv hReplace hm columns hT hS price index A c).trans
    (lifted bits model W k input v hv hReplace hm S hS hT _ (c:ℝ) (by exact_mod_cast hc))

theorem native_one {n T K S : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j)
    (hReplace : (GeneralPaperOriginalValueReduction.run bits model W k input).1.replaced=true)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : FixedArrayTable (GeneralPaperOriginalValueReduction.run bits model W k input).1.m (GeneralPaperQuantizedColumn.Column T K))
    (hT : 0<T) (hS : 0<S) (price index : ℕ → ℕ) (A : ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    GeneralPaperOriginalDrawLaw.law hT hS model o (GeneralPaperNativeCircleLoss.original_representatives_positive bits model W k input) 1
      (run price index A o hm columns).1=
      GeneralPaperNativeSelectedSecurity.lifted bits model W k input v hv hReplace hm S hS hT
        (GeneralPaperDictionary.law (GeneralPaperRowQuantizer.dictionary columns) hT).realRow := by
  have h := GeneralPaperOriginalDrawLaw.original bits model W k input v hv hReplace hm columns hT hS price index A 1
  simpa only [Rat.cast_one,one] using h

end Blotto.GeneralPaperOriginalDrawScale
