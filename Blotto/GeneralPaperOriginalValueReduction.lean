import Blotto.GeneralPaperReducedValuesPrice

/-! Native original-value preparation through the actual reduced array.
Original positive rounding runs once, followed by one classifier/reducer.
The retained first integer weights, denominator and original maps are the
same data needed by reconstruction. Full input accuracy decoding and space
and finite-circle lifting remain separate joins. -/
namespace Blotto.GeneralPaperOriginalValueReduction
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    GeneralPaperReducedValuesDriver.Output n × ℕ :=
  let first := GeneralPaperValueRoundingPaperContract.run bits model W 256 k values
  let reduced := GeneralPaperReducedValuesDriver.run bits model W k first.1.2 first.1.1
  (reduced.1,first.2+reduced.2+128*address bits W (n+reduced.1.m))

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    (run bits model W k values).1=(GeneralPaperReducedValuesDriver.run bits model W k
      (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
      (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.1).1 := rfl

theorem count_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    0<(run bits model W k values).1.m ∧ (run bits model W k values).1.m≤n ∧ (run bits model W k values).1.m<18*2^k := by
  rw [data]
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  exact GeneralPaperReducedValuesDriver.count_bounds bits model W k _ hp.1 _ hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)

theorem positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    ∀ j,0<(run bits model W k values).1.values.read j := by
  change GeneralPaperReducedValuesDriver.Positive (run bits model W k values).1
  rw [data]
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  exact GeneralPaperReducedValuesDriver.positive bits model W k _ hp.1 _ hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)

theorem normalized {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (∑ j,(run bits model W k values).1.values.read j)=1 := by
  change GeneralPaperReducedValuesDriver.Normalized (run bits model W k values).1
  rw [data]
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  exact GeneralPaperReducedValuesDriver.normalized bits model W k _ hp.1 _
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)

noncomputable def selector {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    RationalFieldSelector (run bits model W k values).1.m where
  weight := (run bits model W k values).1.values.read
  positive := positive bits model W k values v hv
  sum_one := normalized bits model W k values v hv

theorem retained {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    (run bits model W k values).1.firstWeights=(GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.1 ∧
      (run bits model W k values).1.denominator=(GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2 := by
  rw [data]
  exact ⟨(GeneralPaperReducedValuesDriver.retained bits model W k _ _).1,
    (GeneralPaperReducedValuesDriver.retained bits model W k _ _).2.1⟩

theorem models_data {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W k values).1=(run false model 1 k values).1 := by
  rw [data,data,GeneralPaperValueRoundingPaperContract.models_data model W 256 k values v hv]
  exact GeneralPaperReducedValuesDriver.models_data model W k _ _

theorem denominator {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W k values).1.denominator≤257*n*2^k := by
  rw [(retained bits model W k values).2]
  have h := (GeneralPaperValueRoundingPaperContract.denominator bits model W 256 k values v hv).2.le
  have hp : 1≤2^k := Nat.one_le_two_pow
  unfold GeneralPaperValueRoundingPaperContract.scale at h
  nlinarith only [h,Nat.mul_le_mul_left n hp]

theorem denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    binaryWordWidth (run bits model W k values).1.denominator≤binaryWordWidth n+k+10 := by
  have h := binaryWordWidth_mono (denominator bits model W k values v hv)
  have h0 := binaryWordWidth_mul (257*n) (2^k)
  have h1 := binaryWordWidth_mul 257 n
  have h257 : binaryWordWidth 257=9 := by decide
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  rw [h257] at h1
  rw [hp] at h0
  omega

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run false model 1 k values).2≤192*(binaryWordWidth k+1)^2+
      GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 256 n k)+210*n+1151 := by
  have hFirst := GeneralPaperValueRoundingPaperContract.arithmetic_work model 256 k values v hv
  have hReduced := GeneralPaperReducedValuesPrice.arithmetic_work model k
    (GeneralPaperValueRoundingPaperContract.run false model 1 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run false model 1 256 k values).1.1
  unfold run
  dsimp only
  simp only [address,Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [hFirst,hReduced]

end Blotto.GeneralPaperOriginalValueReduction
