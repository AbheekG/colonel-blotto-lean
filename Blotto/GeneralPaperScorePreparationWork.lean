import Blotto.GeneralPaperScoreMatrixWork

/-! One cached score stage: arithmetic-only score preparation, the stored
exact-score DP and a final strict scan of that same table. Data erase to the
selected transfer preparation. This source unit profile does not yet join
operand bit prices, simultaneous storage or the other preparation phases.
-/
namespace Blotto.GeneralPaperScorePreparationWork
open GeneralPaperDictionary GeneralPaperMinimum
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (budget : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) :
    (FixedArrayTable (S+1) (Option (Selection K)) × ℕ) × ℕ :=
  let fields := GeneralPaperScoreMatrixWork.fieldsRun w d v S
  let stored := GeneralPaperScoreDPWork.runWithWork S fields.1
  let threshold := GeneralPaperThresholdScanWork.run stored.1 budget
  ((stored.1,threshold.1),fields.2+stored.2+threshold.2+8)

theorem run_data {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (budget : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (run w d budget v S).1=(GeneralPaperComputedThreshold.table d v S,
      GeneralPaperComputedThreshold.compute d budget v S) := by
  simp only [run,GeneralPaperThresholdScanWork.run_data,GeneralPaperScoreDPWork.run_data,
    GeneralPaperScoreMatrixWork.fields_data w d v S hK hCap,
    GeneralPaperComputedThreshold.table,GeneralPaperComputedThreshold.compute]

def profile (m K S w : ℕ) : ℕ :=
  256*(m+1)*(K+1)*(w+1)+256*(m+1)*(S+1)*(K+1)+32*(S+1)+16

theorem run_work {T m K : ℕ} (w : ℕ) (d : Dictionary T m K) (budget : ℚ)
    (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (run w d budget v S).2≤profile m K S w := by
  have hf := GeneralPaperScoreMatrixWork.fields_work w d v S
  have hd := GeneralPaperScoreDPWork.run_work S (GeneralPaperScoreMatrixWork.fieldsRun w d v S).1
  have hs := GeneralPaperThresholdScanWork.run_work
    (GeneralPaperScoreDPWork.runWithWork S (GeneralPaperScoreMatrixWork.fieldsRun w d v S).1).1 budget
  have hLength : (GeneralPaperScoreMatrixWork.fieldsRun w d v S).1.length=m := by
    rw [GeneralPaperScoreMatrixWork.fields_data w d v S hK hCap]
    simp only [GeneralPaperExactScoreDP.fields,List.length_ofFn]
  rw [hLength] at hd
  unfold run profile
  dsimp only
  omega

theorem prepared_data {T m K : ℕ} (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ)
    (v : RationalFieldSelector m) (S w : ℕ) (hCap : S<2^w) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    (run w p.dictionary (opposingProxy/ownBudget) v S).1=(p.table,p.threshold) := by
  dsimp only
  rw [run_data w _ _ v S hK hCap,GeneralPaperTransferPreparation.prepare_table,
    GeneralPaperTransferPreparation.prepare_threshold]

end Blotto.GeneralPaperScorePreparationWork
