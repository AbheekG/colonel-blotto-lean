import Blotto.GeneralPaperThresholdScanBits

/-! The priced stored DP and strict scan for the actual transfer dictionary.
Resource and budget heights come from source rows and proxy budgets. The
input field matrix is already materialized here; its construction, reference
address capacity and whole-preparation coexistence are separate ledger joins.
-/
namespace Blotto.GeneralPaperPreparedScoreBits
open GeneralPaperDictionary GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperStrictScore
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run {K : ℕ} (model : RationalCostModel) (W S : ℕ) (input : List (Field K)) (budget : ℚ) :
    (FixedArrayTable (S+1) (Option (Selection K)) × ℕ) × ℕ :=
  let stored := GeneralPaperScoreDPBits.runWithBits model W S input
  let threshold := GeneralPaperThresholdScanBits.runWithBits model W stored.1 budget
  ((stored.1,threshold.1),stored.2+threshold.2+8*W)

theorem run_data {K : ℕ} (model : RationalCostModel) (W S : ℕ) (input : List (Field K)) (budget : ℚ) :
    (run model W S input budget).1=(GeneralPaperExactScoreDP.run S input,
      GeneralPaperComputedThreshold.scanThreshold (GeneralPaperExactScoreDP.run S input) budget) := by
  simp only [run,GeneralPaperThresholdScanBits.run_data,GeneralPaperScoreDPBits.run_data]

theorem dictionary_data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (d : Dictionary T m K)
    (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) (input : List (Field K))
    (hInput : input=fields (score v S) d.anchor) :
    (run model W S input budget).1=(GeneralPaperComputedThreshold.table d v S,
      GeneralPaperComputedThreshold.compute d budget v S) := by
  rw [run_data,hInput]
  rfl

def profile (model : RationalCostModel) (W m K S A B : ℕ) : ℕ :=
  GeneralPaperScoreDPBits.profile m K S W (model.rat (GeneralPaperScoreBitPrimitive.resourceWidth A m))+
    GeneralPaperThresholdScanBits.profile model W S A m B+8*W

theorem run_work {K : ℕ} (model : RationalCostModel) (W S : ℕ) (input : List (Field K))
    (budget : ℚ) (A B : ℕ) (hHeight : CostHeight input A) (hBudget : RationalHeight budget B)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W S input budget).2≤profile model W input.length K S A B := by
  have hd := GeneralPaperScoreDPBits.run_work model W A S input hHeight hW hIndex
  have hs := GeneralPaperThresholdScanBits.run_work model W A B S input hHeight budget hBudget
  rw [← GeneralPaperScoreDPBits.run_data model W S input] at hs
  change (GeneralPaperScoreDPBits.runWithBits model W S input).2+
    (GeneralPaperThresholdScanBits.runWithBits model W (GeneralPaperScoreDPBits.runWithBits model W S input).1 budget).2+8*W≤_
  unfold profile
  omega

theorem prepared_data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S : ℕ) (input : List (Field K)) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    input=fields (score v S) p.dictionary.anchor →
      (run model W S input (opposingProxy/ownBudget)).1=(p.table,p.threshold) := by
  dsimp only
  intro hInput
  rw [dictionary_data model W _ _ v S input hInput,
    GeneralPaperTransferPreparation.prepare_table,GeneralPaperTransferPreparation.prepare_threshold]

theorem prepared_work {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S A C D : ℕ) (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A)
    (hOwn : RationalHeight ownBudget C) (hOpposing : RationalHeight opposingProxy D)
    (hW : 1≤W) (hIndex : binaryWordWidth (S+2)≤W) (input : List (Field K)) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    input=fields (score v S) p.dictionary.anchor →
      (run model W S input (opposingProxy/ownBudget)).2≤profile model W m K S (A+C) (D+C) := by
  dsimp only
  intro hInput
  have hHeight : CostHeight input (A+C) := by
    rw [hInput]
    exact GeneralPaperQuantizedHeight.fields_cost_height _ v S (A+C)
      (GeneralPaperQuantizedHeight.prepared_height hT hK hDiv rows ownBudget opposingProxy v S A C hRows hOwn)
  have hLength : input.length=m := by rw [hInput]; exact List.length_ofFn
  simpa only [hLength] using run_work model W S input (opposingProxy/ownBudget) (A+C) (D+C)
    hHeight (hOpposing.div hOwn) hW hIndex

theorem materialized_data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S w : ℕ) (hCap : S<2^w) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    (run model W S (GeneralPaperScoreMatrixWork.fieldsRun w p.dictionary v S).1 (opposingProxy/ownBudget)).1=(p.table,p.threshold) := by
  dsimp only
  apply prepared_data model W hT hK hDiv rows ownBudget opposingProxy v S
  exact GeneralPaperScoreMatrixWork.fields_data w _ v S hK hCap

theorem prepared_table_bits {T m K : ℕ} (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S A C : ℕ) (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A) (hOwn : RationalHeight ownBudget C) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    GeneralPaperScoreStoredBits.tableBits W p.table≤4*W+4+(S+1)*(W+GeneralPaperScoreStoredBits.cellBound K W (A+C) m) := by
  dsimp only
  rw [GeneralPaperTransferPreparation.prepare_table]
  have hd := GeneralPaperQuantizedHeight.prepared_height hT hK hDiv rows ownBudget opposingProxy v S A C hRows hOwn
  have hf := GeneralPaperQuantizedHeight.fields_cost_height _ v S (A+C) hd
  simpa only [GeneralPaperComputedThreshold.table,fields,List.length_ofFn] using
    GeneralPaperScoreStoredBits.run_table_bits _ W (A+C) S hf

theorem prepared_score_words {T m K : ℕ} (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S : ℕ) (hIndex : binaryWordWidth (S+2)≤W) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    ∀ f ∈ fields (score v S) p.dictionary.anchor,∀ l,binaryWordWidth (f.read l).1≤W := by
  dsimp only
  exact GeneralPaperScoreDPBits.score_words _ S W (GeneralPaperQuantizedHeight.fields_scores_bound _ v S hK) hIndex

theorem loop_words (m K S W : ℕ) (hScore : binaryWordWidth (S+2)≤W)
    (hLabel : binaryWordWidth (K+2)≤W) (hField : binaryWordWidth (m+2)≤W) :
    (∀ c≤S+1,binaryWordWidth c≤W) ∧ (∀ c≤K+1,binaryWordWidth c≤W) ∧
      (∀ c≤m+1,binaryWordWidth c≤W) := by
  constructor
  · intro c hc
    exact (binaryWordWidth_mono (by omega : c≤S+2)).trans hScore
  · constructor
    · intro c hc
      exact (binaryWordWidth_mono (by omega : c≤K+2)).trans hLabel
    · intro c hc
      exact (binaryWordWidth_mono (by omega : c≤m+2)).trans hField

end Blotto.GeneralPaperPreparedScoreBits
