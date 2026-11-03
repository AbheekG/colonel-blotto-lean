import Blotto.GeneralPaperScoreMatrixBits

/-! Complete bit-priced score stage on an already materialized dictionary:
build the literal matrix, pass that same matrix to the stored DP, retain its
complete table and strictly scan it. Every called stage brings its price.
Source word/reference capacity and selected parameter construction remain
caller obligations; normalization/quantization are separate phases.
-/
namespace Blotto.GeneralPaperScoreStageBits
open GeneralPaperDictionary GeneralPaperMinimum GeneralPaperExactScoreDP GeneralPaperStrictScore
set_option autoImplicit false
set_option maxHeartbeats 1500000

def run {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) :
    (FixedArrayTable (S+1) (Option (Selection K)) × ℕ) × ℕ :=
  let matrix := GeneralPaperScoreMatrixBits.fieldsRun model W w d v S
  let result := GeneralPaperPreparedScoreBits.run model W S matrix.1 budget
  (result.1,matrix.2+result.2+8*W)

theorem run_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (budget : ℚ) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (run model W w d budget v S).1=(GeneralPaperComputedThreshold.table d v S,
      GeneralPaperComputedThreshold.compute d budget v S) := by
  change (GeneralPaperPreparedScoreBits.run model W S
    (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).1 budget).1=_
  exact GeneralPaperPreparedScoreBits.dictionary_data model W d budget v S _
    (GeneralPaperScoreMatrixBits.fields_data model W w d v S hK hCap)

def profile (model : RationalCostModel) (W w m K S V A B : ℕ) : ℕ :=
  GeneralPaperScoreMatrixBits.fieldsProfile model W V A w m K+
    GeneralPaperPreparedScoreBits.profile model W m K S A B+8*W

theorem run_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (budget : ℚ) (v : RationalFieldSelector m) (S V A B : ℕ) (hK : 0<K) (hCap : S<2^w)
    (hValues : ∀ j,RationalHeight (v.weight j) V) (hAnchors : ∀ j l,RationalHeight (d.anchor j l) A)
    (hBudget : RationalHeight budget B) (hW : 1≤W) (hScore : binaryWordWidth (S+2)≤W)
    (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (run model W w d budget v S).2≤profile model W w m K S V A B := by
  have hm := GeneralPaperScoreMatrixBits.fields_work model W w d v S V A hK hCap hValues hAnchors hW hLabel hField
  have hInput := GeneralPaperScoreMatrixBits.fields_data model W w d v S hK hCap
  have hh : CostHeight (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).1 A := by
    rw [hInput]
    exact GeneralPaperQuantizedHeight.fields_cost_height d v S A hAnchors
  have hLength : (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).1.length=m := by
    rw [hInput]
    exact List.length_ofFn
  have hd := GeneralPaperPreparedScoreBits.run_work model W S
    (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).1 budget A B hh hBudget hW hScore
  rw [hLength] at hd
  change (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).2+
    (GeneralPaperPreparedScoreBits.run model W S (GeneralPaperScoreMatrixBits.fieldsRun model W w d v S).1 budget).2+8*W≤_
  unfold profile
  omega

def proxyRun {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m) (S : ℕ) :
    (FixedArrayTable (S+1) (Option (Selection K)) × ℕ) × ℕ :=
  let budget := opposingProxy/ownBudget
  let result := run model W w d budget v S
  (result.1,result.2+GeneralPaperBoundedQuotient.primitivePrice model opposingProxy ownBudget+
    rationalWordWidth budget+8*W)

theorem proxy_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K) (hCap : S<2^w) :
    (proxyRun model W w d ownBudget opposingProxy v S).1=(GeneralPaperComputedThreshold.table d v S,
      GeneralPaperComputedThreshold.compute d (opposingProxy/ownBudget) v S) :=
  run_data model W w d _ v S hK hCap

def proxyProfile (model : RationalCostModel) (W w m K S V A C D : ℕ) : ℕ :=
  profile model W w m K S V A (D+C)+2*model.rat (1+2*(D+C))+8*W

theorem proxy_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (d : Dictionary T m K)
    (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m) (S V A C D : ℕ) (hK : 0<K) (hCap : S<2^w)
    (hValues : ∀ j,RationalHeight (v.weight j) V) (hAnchors : ∀ j l,RationalHeight (d.anchor j l) A)
    (hOwn : RationalHeight ownBudget C) (hOpposing : RationalHeight opposingProxy D)
    (hW : 1≤W) (hScore : binaryWordWidth (S+2)≤W)
    (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    (proxyRun model W w d ownBudget opposingProxy v S).2≤proxyProfile model W w m K S V A C D := by
  have hb := hOpposing.div hOwn
  have hs := run_work model W w d (opposingProxy/ownBudget) v S V A (D+C) hK hCap
    hValues hAnchors hb hW hScore hLabel hField
  have ho := rationalWordWidth_of_height (hOpposing.mono (Nat.le_add_right D C))
  have hw := rationalWordWidth_of_height (hOwn.mono (Nat.le_add_left C D))
  have hp := GeneralPaperBoundedQuotient.primitivePrice_le model opposingProxy ownBudget (1+2*(D+C)) ho hw
  have hc := (rationalWordWidth_of_height hb).trans (model.word_le _)
  unfold proxyRun proxyProfile
  dsimp only
  omega

theorem prepared_data {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S : ℕ) (hCap : S<2^w) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    (proxyRun model W w p.dictionary ownBudget opposingProxy v S).1=(p.table,p.threshold) := by
  dsimp only
  rw [proxy_data model W w _ ownBudget opposingProxy v S hK hCap,
    GeneralPaperTransferPreparation.prepare_table,GeneralPaperTransferPreparation.prepare_threshold]

theorem prepared_work {T m K : ℕ} (model : RationalCostModel) (W w : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (ownBudget opposingProxy : ℚ) (v : RationalFieldSelector m)
    (S V A C D : ℕ) (hCap : S<2^w) (hRows : ∀ i j,RationalHeight ((rows.read i).read j) A)
    (hValues : ∀ j,RationalHeight (v.weight j) V) (hOwn : RationalHeight ownBudget C)
    (hOpposing : RationalHeight opposingProxy D) (hW : 1≤W) (hScore : binaryWordWidth (S+2)≤W)
    (hLabel : binaryWordWidth (K+1)≤W) (hField : binaryWordWidth (m+1)≤W) :
    let p := GeneralPaperTransferPreparation.prepare hT hK hDiv rows ownBudget opposingProxy v S
    (proxyRun model W w p.dictionary ownBudget opposingProxy v S).2≤
      proxyProfile model W w m K S V (A+C) C D := by
  dsimp only
  exact proxy_work model W w _ ownBudget opposingProxy v S V (A+C) C D hK hCap hValues
    (GeneralPaperQuantizedHeight.prepared_height hT hK hDiv rows ownBudget opposingProxy v S A C hRows hOwn)
    hOwn hOpposing hW hScore hLabel hField

end Blotto.GeneralPaperScoreStageBits
