import Blotto.GeneralPaperSourceEndpointBitPrice
import Blotto.GeneralPaperRetainedCompilerBranchBits
import Blotto.GeneralPaperRetainedCompilerSource

/-! Complete local strict-preparation price on actual source columns and
stored values. Heights, maximum and threshold sizes are derived; the same
returned matrix/prepared object feeds endpoint continuation. -/
namespace Blotto.GeneralPaperSourceStrictPreparationBits
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem opposing_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    RationalHeight (opposingBudget m k b reciprocal) (binaryWordWidth (prepare m k).qbar) := by
  cases reciprocal with
  | false => exact GeneralPaperSourceScoreHeights.proxy_height m k b hb
  | true =>
    have hh : RationalHeight (1:ℚ) 1 := by norm_num [RationalHeight]
    exact hh.mono (binaryWordWidth_pos _)

theorem threshold_bound {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) :
    (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.prepared.threshold≤S := by
  change (GeneralPaperRetainedTransferPreparation.threshold true model W
    (GeneralPaperRetainedTransferPreparation.dp true model W S
      (GeneralPaperPhysicalScoreMatrix.run true model W depth columns (GeneralPaperRetainedFieldValues.selector values) S).1.data.toList).1
    (opposing/own)).1≤S
  rw [GeneralPaperRetainedTransferPreparation.threshold_data]
  exact GeneralPaperComputedThreshold.scanThreshold_le _ _

theorem maximum_bound {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hCap : S<2^depth) :
    (GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing).1.maximum≤S := by
  rw [GeneralPaperRetainedTransferPreparation.maximum_data true model W depth S hK columns values own opposing hCap]
  have hh := GeneralPaperComputedThreshold.totalScore_le (GeneralPaperRetainedFieldValues.selector values) S hK
    (fun _ => GeneralPaperScoreMaximum.topLabel K hK)
  simpa only [GeneralPaperStrictScore.totalScore,GeneralPaperScoreMaximum.score_top,GeneralPaperScoreMaximum.maximum] using hh

theorem threshold_price {T m K : ℕ} (model : RationalCostModel) (W depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (own opposing : ℚ) (hCap : S<2^depth) :
    let retained := GeneralPaperRetainedTransferPreparation.run true model W depth S hK columns values own opposing
    GeneralPaperRetainedCompilerBranchBits.thresholdPrice model W retained.1.prepared.threshold retained.1.maximum≤
      model.rat (1+binaryWordWidth S)+32*W := by
  have ht := threshold_bound model W depth S hK columns values own opposing
  have hm := maximum_bound model W depth S hK columns values own opposing hCap
  exact Nat.add_le_add_right (model.monotone (max_le
    (Nat.add_le_add_left (binaryWordWidth_mono ht) 1) (Nat.add_le_add_left (binaryWordWidth_mono hm) 1))) _

def profile (model : RationalCostModel) (W m k Qv : ℕ) : ℕ :=
  GeneralPaperRetainedTransferPrice.bitProfile model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (binaryWordWidth (prepare m k).qbar) (binaryWordWidth (prepare m k).qbar) (binaryWordWidth Qv)
    (GeneralPaperSourceScoreHeights.anchorHeight m k) m (prepare m k).K

theorem actual_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (hW : 1≤W) (hK : binaryWordWidth ((prepare m k).K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hScore : binaryWordWidth ((prepare m k).S+2)≤W) :
    (GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)).2≤profile model W m k Qv := by
  have hv (j : Fin m) : RationalHeight (values.values.read j) (binaryWordWidth Qv) := by
    change RationalHeight ((GeneralPaperRetainedFieldValues.selector values).weight j) _
    rw [hValues]
    exact GeneralPaperSourceScoreHeights.value_height Qv hQv weights hp hs j
  have hc (j : Fin m) (l : Fin (prepare m k).K) :
      RationalHeight ((columns.read j).anchors.read l) (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
    change RationalHeight ((GeneralPaperRowQuantizer.dictionary columns).anchor j l) _
    rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
    exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l
  exact GeneralPaperRetainedTransferPrice.bit_work model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    _ _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
    (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal) (opposing_height m k b hb reciprocal)
    hv hc (GeneralPaperScoreScaleParameters.score_cap m k) hW hK hM hScore

theorem actual_prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    (GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)).1.prepared=
        GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal := by
  have hData := GeneralPaperRetainedBitData.transfer model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperScoreScaleParameters.score_cap m k)
  exact (congrArg (fun o => o.prepared) hData).trans
    (GeneralPaperRetainedCompilerSource.prepared model k Qv hQv weights hp hs b reciprocal columns values hColumns hValues)

theorem actual_matrix {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal)
    (hValues : GeneralPaperRetainedFieldValues.selector values=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) :
    (GeneralPaperRetainedTransferPreparation.run true model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)).1.matrix=
      (GeneralPaperScoreMatrixWork.matrixRun (GeneralPaperScoreScaleParameters.prepare m k).depth
        (GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal).dictionary
        (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S).1 := by
  have hData := GeneralPaperRetainedBitData.transfer model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperScoreScaleParameters.score_cap m k)
  have hMat := GeneralPaperRetainedCompilerBranch.matrix model (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
    (GeneralPaperScoreScaleParameters.labels_positive m k) columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperScoreScaleParameters.score_cap m k)
  dsimp only at hMat
  erw [GeneralPaperRetainedCompilerSource.prepared model k Qv hQv weights hp hs b reciprocal columns values hColumns hValues,hValues] at hMat
  exact (congrArg (fun o => o.matrix) hData).trans hMat

end Blotto.GeneralPaperSourceStrictPreparationBits
