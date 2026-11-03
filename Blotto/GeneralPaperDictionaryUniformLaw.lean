import Blotto.GeneralPaperCircleCanonicalLift

/-! The selected source pair's actual canonical laws are uniform whole-row
laws, including the original real poor-budget scaling. Repeated rows remain
distinct uniform labels; no product of coordinate marginals is substituted. -/
namespace Blotto.GeneralPaperDictionaryUniformLaw
open MeasureTheory GeneralPaperDictionary
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem dictionary {T m K : ℕ} (d : Dictionary T m K) (hT : 0<T) :
    GeneralPaperUniformRowLaw.law hT (law d hT).realRow=(law d hT).law := by
  have hw : (law d hT).realWeight=(fun _:Fin T => 1/(T:ℝ)) := by
    funext i
    simp only [law,RationalWholeRowLaw.realWeight,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  apply ProbabilityMeasure.toMeasure_injective
  change mixtureMeasure (fun _:Fin T => 1/(T:ℝ))
    (fun i => GeneralPaperUniformRowLaw.point ((law d hT).realRow i))=
      mixtureMeasure (law d hT).realWeight (fun i => ProductBidTree.allocationPointLaw ((law d hT).realRow i))
  rw [hw]
  rfl

theorem scaled_uniform {n T : ℕ} (hT : 0<T) (rows : Fin T → Allocation n) (c : ℝ) :
    scaleLaw c (GeneralPaperUniformRowLaw.law hT rows)=
      GeneralPaperUniformRowLaw.law hT (fun r => scaleAllocation c (rows r)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (scaleAllocation c) (mixtureMeasure (fun _:Fin T => 1/(T:ℝ))
    (fun r => GeneralPaperUniformRowLaw.point (rows r)))=
      mixtureMeasure (fun _:Fin T => 1/(T:ℝ)) (fun r => GeneralPaperUniformRowLaw.point (scaleAllocation c (rows r)))
  rw [mixtureMeasure_map _ _ _ (measurable_scaleAllocation c)]
  unfold mixtureMeasure
  congr 1
  funext r
  change ENNReal.ofReal (1/(T:ℝ)) • Measure.map (scaleAllocation c) (Measure.dirac (rows r))=_
  rw [Measure.map_dirac' (measurable_scaleAllocation c)]
  rfl

theorem rich {T m K : ℕ} (pair : GeneralPaperSourcePairRun.Pair T m K) (hT : 0<T) :
    GeneralPaperSourcePairCanonical.richLaw pair hT=
      GeneralPaperUniformRowLaw.law hT (law pair.rich hT).realRow := (dictionary pair.rich hT).symm

theorem poor {T m K : ℕ} (pair : GeneralPaperSourcePairRun.Pair T m K) (hT : 0<T) (b : ℝ) :
    GeneralPaperSourcePairCanonical.poorLaw pair hT b=
      GeneralPaperUniformRowLaw.law hT (fun r => scaleAllocation b ((law pair.poor hT).realRow r)) := by
  unfold GeneralPaperSourcePairCanonical.poorLaw
  rw [←dictionary pair.poor hT,scaled_uniform]

end Blotto.GeneralPaperDictionaryUniformLaw
