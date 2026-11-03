import Blotto.GeneralPaperRetainedBitData
import Blotto.GeneralPaperRetainedCompilerBranch

/-! The modified branch uses bit prices throughout its complete strict
preparation and retained basis endpoint. A maximal threshold returns the
zero tag before initializer/basis/reciprocal continuation. The reached
output tag's reciprocal is priced separately from endpoint computation. -/
namespace Blotto.GeneralPaperRetainedCompilerBranchBits
open GeneralPaperSourceEndpointBranch GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000

def thresholdPrice (model : RationalCostModel) (W threshold maximum : ℕ) : ℕ :=
  model.rat (max (1+binaryWordWidth threshold) (1+binaryWordWidth maximum))+32*W

def tagPrice (model : RationalCostModel) (W : ℕ) (reciprocal : Bool) (value : ℚ) : ℕ :=
  (if reciprocal then GeneralPaperRationalPrimitivePrice.binary model.rat (fun x y => x/y) 1 value
    else model.rat (rationalWordWidth value))+32*W

def run {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) : Option (Result T m K)×ℕ :=
  let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values ownBudget opposingProxy
  let prep := retained.1.prepared
  let test := thresholdPrice model W prep.threshold retained.1.maximum
  if prep.threshold=retained.1.maximum then
    (some ⟨prep.dictionary.label,.zero⟩,retained.2+test+64*W) else
    let result := GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal prep retained.1.matrix endpoint value
    (result.1.map (fun point => ⟨prep.dictionary.label,.endpoint (if reciprocal then 1/value else value) point⟩),
      retained.2+test+result.2+(if result.1.isSome then tagPrice model W reciprocal value else 0)+80*W)

theorem data {T m : ℕ} (model : RationalCostModel) (W k p q : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (hValue : endpoint.value=value)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H p q
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy reciprocal endpoint value).1=
      (GeneralPaperRetainedCompilerBranch.run model (GeneralPaperScoreScaleParameters.prepare m k).depth
        (prepare m k).S (prepare m k).H p q (GeneralPaperScoreScaleParameters.labels_positive m k)
        columns values ownBudget opposingProxy reciprocal endpoint value).1 := by
  let retained := GeneralPaperRetainedTransferPreparation.run false model 1 (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy
  have hRet := GeneralPaperRetainedBitData.transfer model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy
    (GeneralPaperScoreScaleParameters.score_cap m k)
  have hMat := GeneralPaperRetainedCompilerBranch.matrix model (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy
    (GeneralPaperScoreScaleParameters.score_cap m k)
  have hNew := GeneralPaperRetainedBasisEndpointBits.data model W k p q reciprocal retained.1.prepared
    (GeneralPaperRetainedFieldValues.selector values) retained.1.matrix hMat endpoint value hValue hm hp hq
  have hOld := GeneralPaperRetainedBasisEndpoint.data model k p q reciprocal retained.1.prepared
    (GeneralPaperRetainedFieldValues.selector values) retained.1.matrix hMat endpoint value hValue hm hp hq
  have hBasis := hNew.trans hOld.symm
  dsimp only [run,GeneralPaperRetainedCompilerBranch.run]
  rw [hRet]
  split
  · rfl
  · erw [hBasis]
    rfl

theorem labels {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (result : Result T m K)
    (hr : (run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1=some result) :
    (GeneralPaperRowQuantizer.dictionary columns).label=result.labels := by
  dsimp only [run] at hr
  split at hr
  · cases Option.some.inj hr
    rfl
  · obtain ⟨point,_,he⟩ := Option.map_eq_some_iff.mp hr
    cases he
    rfl

theorem work {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values ownBudget opposingProxy
    (run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).2≤
      retained.2+thresholdPrice model W retained.1.prepared.threshold retained.1.maximum+
      (if retained.1.prepared.threshold=retained.1.maximum then 0 else
        (GeneralPaperRetainedBasisEndpointBits.run model W H p q reciprocal retained.1.prepared retained.1.matrix endpoint value).2+
          tagPrice model W reciprocal value)+80*W := by
  dsimp only [run]
  split_ifs <;> omega

end Blotto.GeneralPaperRetainedCompilerBranchBits
