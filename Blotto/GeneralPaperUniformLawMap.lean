import Blotto.GeneralPaperOriginalCirclePointwise

/-! Exact measurable maps of whole-law uniform mixtures. These identities
retain row dependence and the common shift, and permit original names and
budget units to be applied to the actual nested finite output law. -/
namespace Blotto.GeneralPaperUniformLawMap
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem mixture {m n T : ℕ} (f : Allocation m → Allocation n) (hf : Measurable f) (hT : 0<T) (laws : Fin T → Mixed m) :
    (GeneralPaperUniformRowLaw.mixture hT laws).map f=
      GeneralPaperUniformRowLaw.mixture hT (fun r => (laws r).map f) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map f (mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) laws)=
    mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) (fun r => (laws r).map f)
  rw [mixtureMeasure_map _ _ f hf]
  rfl

theorem relabel_mixture {m n T : ℕ} (e : Fin m ≃ Fin n) (hT : 0<T) (laws : Fin T → Mixed n) :
    GeneralPaperFieldRelabel.law e (GeneralPaperUniformRowLaw.mixture hT laws)=
      GeneralPaperUniformRowLaw.mixture hT (fun r => GeneralPaperFieldRelabel.law e (laws r)) :=
  mixture _ (GeneralPaperFieldRelabel.measurable_allocation e) hT laws

theorem scale_mixture {n T : ℕ} (c : ℝ) (hT : 0<T) (laws : Fin T → Mixed n) :
    scaleLaw c (GeneralPaperUniformRowLaw.mixture hT laws)=
      GeneralPaperUniformRowLaw.mixture hT (fun r => scaleLaw c (laws r)) :=
  mixture _ (measurable_scaleAllocation c) hT laws

theorem relabel_scale {m n : ℕ} (e : Fin m ≃ Fin n) (c : ℝ) (μ : Mixed n) :
    GeneralPaperFieldRelabel.law e (scaleLaw c μ)=scaleLaw c (GeneralPaperFieldRelabel.law e μ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (GeneralPaperFieldRelabel.allocation e) (Measure.map (scaleAllocation c) (μ:Measure (Allocation n)))=
    Measure.map (scaleAllocation c) (Measure.map (GeneralPaperFieldRelabel.allocation e) (μ:Measure (Allocation n)))
  rw [Measure.map_map (GeneralPaperFieldRelabel.measurable_allocation e) (measurable_scaleAllocation c),
    Measure.map_map (measurable_scaleAllocation c) (GeneralPaperFieldRelabel.measurable_allocation e)]
  rfl

theorem circle_row_scale {h g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (x : Allocation (h+R)) (c : ℝ) (hc : 0<c) (shift : ℕ) :
    GeneralPaperCircleCanonicalLift.row R W hR hW weights (scaleAllocation c x) shift=
      scaleAllocation c (GeneralPaperCircleCanonicalLift.row R W hR hW weights x shift) :=
  GeneralPaperCircleSortedScale.reconstructed_scale R W hR hW weights
    (GeneralPaperCircleCanonicalLift.kept x) (GeneralPaperCircleCanonicalLift.representatives x) c hc shift

theorem selected_scale {h g T : ℕ} (R W S : ℕ) (hR : 0<R) (hW : 0<W) (hS : 0<S) (hT : 0<T)
    (weights : Fin g → ℕ) (rows : Fin T → Allocation (h+R)) (c : ℝ) (hc : 0<c) :
    scaleLaw c (GeneralPaperSelectedCircleLaw.law R W S hR hW hS hT weights rows)=
      GeneralPaperSelectedCircleLaw.law R W S hR hW hS hT weights (fun r => scaleAllocation c (rows r)) := by
  unfold GeneralPaperSelectedCircleLaw.law
  rw [scale_mixture]
  congr 1
  funext r
  rw [GeneralPaperDictionaryUniformLaw.scaled_uniform]
  congr 1
  funext l
  exact (circle_row_scale R W hR hW weights (rows r) c hc _).symm

end Blotto.GeneralPaperUniformLawMap
