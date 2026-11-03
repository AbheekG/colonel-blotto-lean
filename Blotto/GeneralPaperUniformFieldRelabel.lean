import Blotto.GeneralPaperNativeReductionShape

/-! Exact relabeling of finite uniform whole-row laws. This identifies the
source's native dimension with the retained-plus-representative index type. -/
namespace Blotto.GeneralPaperUniformFieldRelabel
open MeasureTheory
set_option autoImplicit false

theorem uniform {m n T : ℕ} (e : Fin m ≃ Fin n) (hT : 0<T) (rows : Fin T → Allocation n) :
    GeneralPaperFieldRelabel.law e (GeneralPaperUniformRowLaw.law hT rows)=
      GeneralPaperUniformRowLaw.law hT (fun r => GeneralPaperFieldRelabel.allocation e (rows r)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (GeneralPaperFieldRelabel.allocation e)
    (mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) (fun r => GeneralPaperUniformRowLaw.point (rows r)))=
      mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) (fun r => GeneralPaperUniformRowLaw.point (GeneralPaperFieldRelabel.allocation e (rows r)))
  rw [mixtureMeasure_map _ _ _ (GeneralPaperFieldRelabel.measurable_allocation e)]
  unfold mixtureMeasure
  congr 1
  funext r
  change ENNReal.ofReal (1/(T:ℝ)) • Measure.map (GeneralPaperFieldRelabel.allocation e) (Measure.dirac (rows r))=_
  rw [Measure.map_dirac' (GeneralPaperFieldRelabel.measurable_allocation e)]
  rfl

theorem security {m n T : ℕ} (e : Fin m ≃ Fin n) (hT : 0<T) (rows : Fin T → Allocation n) (v : Values n) (B : ℝ) :
    Blotto.security (GeneralPaperFieldRelabel.values e v) B
      (GeneralPaperUniformRowLaw.law hT (fun r => GeneralPaperFieldRelabel.allocation e (rows r)))=
      Blotto.security v B (GeneralPaperUniformRowLaw.law hT rows) := by
  rw [←uniform,GeneralPaperFieldRelabel.security_relabel]

end Blotto.GeneralPaperUniformFieldRelabel
