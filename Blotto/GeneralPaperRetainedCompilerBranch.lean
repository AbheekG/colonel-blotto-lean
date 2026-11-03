import Blotto.GeneralPaperRetainedBasisEndpoint
import Blotto.GeneralPaperCheckedEndpointBranch

/-! Once-only arithmetic modified-defender branch. A single physical
matrix feeds the complete DP, strict scan, stored maximum, basis and final
checks. A maximum threshold returns the zero tag before initializer/basis
or reciprocal evaluation. Source rows and quantization are already retained. -/
namespace Blotto.GeneralPaperRetainedCompilerBranch
open GeneralPaperSourceEndpointBranch GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) : Option (Result T m K)×ℕ :=
  let retained := GeneralPaperRetainedTransferPreparation.run false model 1 depth S hK columns values ownBudget opposingProxy
  let prep := retained.1.prepared
  if prep.threshold=retained.1.maximum then
    (some ⟨prep.dictionary.label,.zero⟩,retained.2+64) else
    let result := GeneralPaperRetainedBasisEndpoint.run model H p q reciprocal prep retained.1.matrix endpoint value
    ((result.1.map (fun point => ⟨prep.dictionary.label,.endpoint (if reciprocal then 1/value else value) point⟩)),
      retained.2+result.2+80)

theorem matrix {T m K : ℕ} (model : RationalCostModel) (depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ) (hCap : S<2^depth) :
    let retained := GeneralPaperRetainedTransferPreparation.run false model 1 depth S hK columns values ownBudget opposingProxy
    retained.1.matrix=(GeneralPaperScoreMatrixWork.matrixRun depth retained.1.prepared.dictionary
      (GeneralPaperRetainedFieldValues.selector values) S).1 := by
  dsimp only
  rw [GeneralPaperRetainedTransferPreparation.matrix_data,
    GeneralPaperRetainedTransferPreparation.data false model 1 depth S hK columns values ownBudget opposingProxy hCap,
    GeneralPaperPhysicalScoreMatrix.data false model 1 depth columns _ S hK hCap,
    GeneralPaperScoreMatrixWork.matrix_data depth _ _ S hK hCap]
  rfl

theorem data {T m : ℕ} (model : RationalCostModel) (k p q : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (hValue : endpoint.value=value)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    let depth := (GeneralPaperScoreScaleParameters.prepare m k).depth
    let hK : 0 < (prepare m k).K := GeneralPaperScoreScaleParameters.labels_positive m k
    let retained := GeneralPaperRetainedTransferPreparation.run false model 1 depth (prepare m k).S hK columns values ownBudget opposingProxy
    let prep := retained.1.prepared
    let v := GeneralPaperRetainedFieldValues.selector values
    (run model depth (prepare m k).S (prepare m k).H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1=
      if prep.threshold=GeneralPaperScoreMaximum.maximum v (prepare m k).S then some ⟨prep.dictionary.label,.zero⟩ else
        (GeneralPaperCheckedBasisEndpoint.run k prep v p q value reciprocal).map
          (fun point => ⟨prep.dictionary.label,.endpoint (if reciprocal then 1/value else value) point⟩) := by
  dsimp only
  have hCap := GeneralPaperScoreScaleParameters.score_cap m k
  have hMat := matrix model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy hCap
  have hBasis := GeneralPaperRetainedBasisEndpoint.data model k p q reciprocal _ _ _ hMat endpoint value hValue hm hp hq
  have hMax := GeneralPaperRetainedTransferPreparation.maximum_data (K := (prepare m k).K)
    false model 1 (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy hCap
  simp only [run]
  rw [hMax]
  split
  · rfl
  · exact congrArg (Option.map (fun point =>
      (⟨(GeneralPaperRetainedTransferPreparation.run false model 1 (GeneralPaperScoreScaleParameters.prepare m k).depth
        (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy).1.prepared.dictionary.label,
        .endpoint (if reciprocal then 1/value else value) point⟩ : Result T m (prepare m k).K))) hBasis

theorem labels {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (result : Result T m K)
    (hr : (run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1=some result) :
    (GeneralPaperRowQuantizer.dictionary columns).label=result.labels := by
  dsimp only [run] at hr
  split at hr
  · cases Option.some.inj hr
    rfl
  · obtain ⟨point,_,he⟩ := Option.map_eq_some_iff.mp hr
    cases he
    rfl

end Blotto.GeneralPaperRetainedCompilerBranch
