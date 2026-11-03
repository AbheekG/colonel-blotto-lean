import Blotto.GeneralPaperRetainedTransferPreparation

/-! Complete local time prices for the actual retained strict-score
preparation. The whole DP and maximum use the same matrix; rational budget
division, list materialization and reference/control writes are included. -/
namespace Blotto.GeneralPaperRetainedTransferPrice
open GeneralPaperRetainedTransferPreparation GeneralPaperExactScoreDP GeneralPaperScoreBitPrimitive
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution GeneralPaperBoundedQuotient
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3600000

def arithmeticProfile (m K S depth : ℕ) : ℕ :=
  128*(m+1)*(K+1)*(depth+1)+64*m*K+256*(m+1)*(S+1)*(K+1)+32*(S+1)+320*(m+1)+74

theorem arithmetic_work {T m K : ℕ} (model : RationalCostModel) (depth S : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) :
    (run false model 1 depth S hK columns values ownBudget opposingProxy).2≤arithmeticProfile m K S depth := by
  let v := GeneralPaperRetainedFieldValues.selector values
  let matrix := GeneralPaperPhysicalScoreMatrix.run false model 1 depth columns v S
  let fields := matrix.1.data.toList
  have hLen : fields.length=m := by dsimp only [fields];rw [Array.length_toList,matrix.1.size]
  have hMat := GeneralPaperPhysicalScoreMatrix.arithmetic_work model depth columns v S
  have hDP := GeneralPaperScoreDPWork.run_work S fields
  rw [hLen] at hDP
  have hScan := GeneralPaperThresholdScanWork.run_work (dp false model 1 S fields).1 (opposingProxy/ownBudget)
  have hMax := GeneralPaperStoredScoreMaximum.arithmetic_work model hK matrix.1
  change matrix.2+(dp false model 1 S fields).2+(threshold false model 1 (dp false model 1 S fields).1 (opposingProxy/ownBudget)).2+
    (GeneralPaperStoredScoreMaximum.run false model 1 hK matrix.1).2+
    GeneralPaperRationalPrimitivePrice.binary (fun _ => 1) (fun a b => a/b) opposingProxy ownBudget+64*(m+1)*1+64*1≤_
  change (dp false model 1 S fields).2≤_ at hDP
  change (threshold false model 1 (dp false model 1 S fields).1 (opposingProxy/ownBudget)).2≤_ at hScan
  change matrix.2≤_ at hMat
  unfold arithmeticProfile
  simp only [GeneralPaperRationalPrimitivePrice.binary]
  nlinarith only [hMat,hDP,hScan,hMax]

def bitProfile (model : RationalCostModel) (W depth S C D V H m K : ℕ) : ℕ :=
  GeneralPaperScoreMatrixBits.matrixProfile model W V H depth m K+64*m*K*arrayWord W (m*K+m+K)+
    GeneralPaperScoreDPBits.profile m K S W (model.rat (resourceWidth H m))+
    GeneralPaperThresholdScanBits.profile model W S H m (C+D)+
    (m*(2*model.rat (1+binaryWordWidth S)+256*arrayWord W m)+160*arrayWord W m+2*model.rat (1+binaryWordWidth K))+
    2*model.rat (1+2*(C+D))+64*(m+1)*arrayWord W (m+K+S)+64*arrayWord W (m+K+S)

theorem bit_work {T m K : ℕ} (model : RationalCostModel) (W depth S C D V H : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (values : GeneralPaperRetainedFieldValues.Values m)
    (ownBudget opposingProxy : ℚ) (hOwn : RationalHeight ownBudget C) (hOpposing : RationalHeight opposingProxy D)
    (hValues : ∀ j,RationalHeight (values.values.read j) V) (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H)
    (hCap : S<2^depth) (hW : 1≤W) (hLabel : binaryWordWidth (K+1)≤W)
    (hField : binaryWordWidth (m+1)≤W) (hScore : binaryWordWidth (S+2)≤W) :
    (run true model W depth S hK columns values ownBudget opposingProxy).2≤bitProfile model W depth S C D V H m K := by
  let v := GeneralPaperRetainedFieldValues.selector values
  let matrix := GeneralPaperPhysicalScoreMatrix.run true model W depth columns v S
  let fields := matrix.1.data.toList
  let budget := opposingProxy/ownBudget
  have hBudget : RationalHeight budget (C+D) := by
    simpa only [Nat.add_comm] using hOpposing.div hOwn
  have hfData := fields_data true model W depth S columns v hK hCap
  change fields=GeneralPaperExactScoreDP.fields (GeneralPaperStrictScore.score v S) (GeneralPaperRowQuantizer.dictionary columns).anchor at hfData
  have hFields : CostHeight fields H := by
    rw [hfData]
    exact GeneralPaperQuantizedHeight.fields_cost_height _ v S H hColumns
  have hLen : fields.length=m := by dsimp only [fields];rw [Array.length_toList,matrix.1.size]
  have hMat := GeneralPaperPhysicalScoreMatrix.bit_work model W depth V H columns v S hK hCap hValues hColumns hW hLabel hField
  have hDP := GeneralPaperScoreDPBits.run_work model W H S fields hFields hW hScore
  rw [hLen] at hDP
  have hScan := GeneralPaperThresholdScanBits.run_work model W H (C+D) S fields hFields budget hBudget
  rw [hLen] at hScan
  have hScan' : (threshold true model W (dp true model W S fields).1 budget).2≤
      GeneralPaperThresholdScanBits.profile model W S H m (C+D) := by
    change (GeneralPaperThresholdScanBits.runWithBits model W (dp true model W S fields).1 budget).2≤_
    rw [dp_data]
    exact hScan
  have hBound : (∑ j,((matrix.1.read j).read (GeneralPaperScoreMaximum.topLabel K hK)).1)≤S := by
    dsimp only [matrix]
    rw [GeneralPaperPhysicalScoreMatrix.data true model W depth columns v S hK hCap]
    simpa only [FixedArrayTable.read_ofFn,GeneralPaperStrictScore.totalScore] using
      GeneralPaperComputedThreshold.totalScore_le v S hK (fun _ => GeneralPaperScoreMaximum.topLabel K hK)
  have hMax := GeneralPaperStoredScoreMaximum.bit_work model W S hK matrix.1 hBound
  have hDiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    opposingProxy ownBudget (1+2*(C+D)) ((rationalWordWidth_of_height hOpposing).trans (by omega))
    ((rationalWordWidth_of_height hOwn).trans (by omega)) (rationalWordWidth_of_height hBudget)
  change matrix.2+(dp true model W S fields).2+(threshold true model W (dp true model W S fields).1 budget).2+
    (GeneralPaperStoredScoreMaximum.run true model W hK matrix.1).2+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) opposingProxy ownBudget+
    64*(m+1)*arrayWord W (m+K+S)+64*arrayWord W (m+K+S)≤_
  change (dp true model W S fields).2≤_ at hDP
  change matrix.2≤_ at hMat
  unfold bitProfile
  omega

end Blotto.GeneralPaperRetainedTransferPrice
