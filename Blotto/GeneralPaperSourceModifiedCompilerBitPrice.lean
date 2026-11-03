import Blotto.GeneralPaperSourceStrictPreparationBits
import Blotto.GeneralPaperRetainedModifiedColumnBits

/-! Complete local selected-defender price: strict preparation, bounded
threshold test, full endpoint driver, reached tag and endpoint columns.
The actual source/value identities discharge all height/magnitude bounds;
no basis, feasibility, score or size certificate is supplied at runtime. -/
namespace Blotto.GeneralPaperSourceModifiedCompilerBitPrice
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

theorem sum_bound (p t e g A B C D W : ℕ) (test : Prop) [Decidable test]
    (hp : p≤A) (ht : t≤B+32*W) (he : e≤C) (hg : g≤D+32*W) :
    p+t+(if test then 0 else e+g)+80*W≤A+B+C+D+144*W := by
  split_ifs <;> omega

def branchProfile (model : RationalCostModel) (W m k Qv p q : ℕ) (reciprocal : Bool) : ℕ :=
  GeneralPaperSourceStrictPreparationBits.profile model W m k Qv+model.rat (1+binaryWordWidth (prepare m k).S)+
  GeneralPaperSourceEndpointBitPrice.profile model W m k p q reciprocal+
  6*model.rat (GeneralPaperRetainedEndpointBitBounds.priceWidth (prepare m k).qbar)+144*W

theorem branch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) :
    let classified := GeneralPaperProxyClassifier.classify m k b
    let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) classified).1
    (GeneralPaperRetainedCompilerBranchBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H classified.choice.proxy.num classified.choice.proxy.den (GeneralPaperScoreScaleParameters.labels_positive m k)
      columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint classified.choice.endpoint).2≤
        branchProfile model W m k Qv classified.choice.proxy.num classified.choice.proxy.den reciprocal := by
  dsimp only
  let classified := GeneralPaperProxyClassifier.classify m k b
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) classified).1
  let retained := GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
  have hPrep := GeneralPaperSourceStrictPreparationBits.actual_prepared model W k Qv hQv weights hp hs b reciprocal columns values hColumns hValues
  have hMatrix := GeneralPaperSourceStrictPreparationBits.actual_matrix model W k Qv hQv weights hp hs b reciprocal columns values hColumns hValues
  have hStrict := GeneralPaperSourceStrictPreparationBits.actual_work model W k Qv hQv weights hp hs b hb reciprocal columns values hColumns hValues hW hK hM hIndex
  have hTest := GeneralPaperSourceStrictPreparationBits.threshold_price model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) (GeneralPaperScoreScaleParameters.score_cap m k)
  have hEndpoint := GeneralPaperSourceEndpointBitPrice.actual_work model W k Qv hm hQv weights hp hs b hb reciprocal hModify
    retained.1.matrix hMatrix hW hDim hK hM hIndex hBatch hFinal
  have hEndpointEq := congrArg (fun p => (GeneralPaperRetainedBasisEndpointBits.run model W (prepare m k).H
    classified.choice.proxy.num classified.choice.proxy.den reciprocal p retained.1.matrix endpoint classified.choice.endpoint).2) hPrep
  have hEndpointActual := hEndpointEq.le.trans hEndpoint
  have hBounds := GeneralPaperRetainedEndpointBitBounds.fraction_bounds model.rat W m k b hb hModify
  have hHeight := GeneralPaperEndpointRatioSize.height m k b hb hModify
  have hFractionPrice := GeneralPaperRetainedEndpointBitBounds.endpoint_price model W (prepare m k).qbar endpoint
    classified.choice.endpoint hBounds.1 hBounds.2 hHeight reciprocal
  have hTag : GeneralPaperRetainedCompilerBranchBits.tagPrice model W reciprocal classified.choice.endpoint≤
      GeneralPaperRetainedBasisEndpointBits.endpointPrice model W endpoint classified.choice.endpoint reciprocal := by
    unfold GeneralPaperRetainedCompilerBranchBits.tagPrice GeneralPaperRetainedBasisEndpointBits.endpointPrice
    omega
  have hTagBound := hTag.trans hFractionPrice
  have hBranch := GeneralPaperRetainedCompilerBranchBits.work model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (prepare m k).H classified.choice.proxy.num classified.choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint classified.choice.endpoint
  exact hBranch.trans (sum_bound _ _ _ _ _ _ _ _ W _ hStrict hTest hEndpointActual hTagBound)

def columnProfile (model : RationalCostModel) (W m k Qv p q : ℕ) (reciprocal : Bool) : ℕ :=
  branchProfile model W m k Qv p q reciprocal+
    GeneralPaperRetainedModifiedColumnBits.columnProfile model W m (prepare m k).K+64*W

theorem column_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hDim : binaryWordWidth (m*((prepare m k).K-1)+3)≤W)
    (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth ((prepare m k).S+2)≤W)
    (hBatch : binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤W)
    (hFinal : binaryWordWidth ((prepare m k).S+4)≤W) (hColumnsIndex : binaryWordWidth (m+(prepare m k).K+1)≤W) :
    let classified := GeneralPaperProxyClassifier.classify m k b
    let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) classified).1
    (GeneralPaperRetainedModifiedColumnBits.run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (prepare m k).H classified.choice.proxy.num classified.choice.proxy.den (GeneralPaperScoreScaleParameters.labels_positive m k)
      columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint classified.choice.endpoint).2≤
        columnProfile model W m k Qv classified.choice.proxy.num classified.choice.proxy.den reciprocal := by
  dsimp only
  let classified := GeneralPaperProxyClassifier.classify m k b
  let endpoint := (GeneralPaperRetainedEndpointFraction.run model.rat W (prepare m k).Qg (grid_positive m k) classified).1
  have hBranch := branch_work model W k Qv hm hQv weights hp hs b hb reciprocal hModify columns values hColumns hValues
    hW hDim hK hM hIndex hBatch hFinal
  have hColumnsWork := GeneralPaperRetainedModifiedColumnBits.work model W (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepare m k).S (prepare m k).H classified.choice.proxy.num classified.choice.proxy.den
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal) reciprocal endpoint classified.choice.endpoint hW hColumnsIndex
  exact hColumnsWork.trans (Nat.add_le_add_right (Nat.add_le_add_right hBranch _) _)

end Blotto.GeneralPaperSourceModifiedCompilerBitPrice
