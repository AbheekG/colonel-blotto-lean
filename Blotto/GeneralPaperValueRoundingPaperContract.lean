import Blotto.GeneralPaperValueRoundingInputPrice

/-! Construct the paper's integer scale from n and the selected dyadic
exponent, then run positive rounding once. Both original and reduced-value
roundings return positive integer source weights and a short denominator.
Input accuracy decoding, reduction/lifting and full input storage are later
joins; no such completion is inferred from this value-processing component. -/
namespace Blotto.GeneralPaperValueRoundingPaperContract
open GeneralPaperDecodeBucketExecution (primitive)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 8192

def scale (c n k : ℕ) : ℕ := c*n*2^k

def scaleRun (bits : Bool) (model : RationalCostModel) (W c n k : ℕ) : ℕ × ℕ :=
  let power := if bits then
    let result := GeneralPaperNatPowerBits.run model.rat W 2 k
    (result.1.power,result.2)
    else GeneralPaperPhysicalPowerArithmetic.run 2 k
  (c*n*power.1,power.2+
    GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a*b) c n+
    GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a*b) (c*n) power.1+128*W)

theorem scale_data (bits : Bool) (model : RationalCostModel) (W c n k : ℕ) : (scaleRun bits model W c n k).1=scale c n k := by
  cases bits
  · unfold scaleRun scale
    simp only [Bool.false_eq_true,ite_false,GeneralPaperPhysicalPowerArithmetic.data]
  · unfold scaleRun scale
    simp only [ite_true,GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data 2 k).1]

def scaleBitProfile (model : RationalCostModel) (W c n k : ℕ) : ℕ :=
  64*(binaryWordWidth k+1)*(W+model.rat (GeneralPaperNatPowerOperands.width 2 k))+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) c n+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) (c*n) (2^k)+128*W

theorem scale_bit_work (model : RationalCostModel) (W c n k : ℕ) :
    (scaleRun true model W c n k).2≤scaleBitProfile model W c n k := by
  have h := GeneralPaperNatPowerBits.work model.rat model.monotone W 2 k (by decide)
  unfold scaleRun scaleBitProfile
  simp only [ite_true,primitive,GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data 2 k).1]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right h _) _) _

theorem scale_arithmetic_work (model : RationalCostModel) (c n k : ℕ) :
    (scaleRun false model 1 c n k).2≤64*(binaryWordWidth k+1)^2+132 := by
  have h := GeneralPaperPhysicalPowerArithmetic.work 2 k
  unfold scaleRun
  simp only [Bool.false_eq_true,ite_false,primitive,GeneralPaperNaturalPrimitivePrice.binary,Nat.mul_one]
  nlinarith only [h]

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ) :
    (FixedArrayTable n ℕ × ℕ) × ℕ :=
  let constructed := scaleRun bits model W c n k
  let rounded := GeneralPaperValueRoundingDriver.run bits model W constructed.1 values
  (rounded.1,constructed.2+rounded.2+128*W)

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ) :
    (run bits model W c k values).1=(GeneralPaperValueRoundingDriver.run bits model W (scale c n k) values).1 := by
  unfold run
  dsimp only
  rw [scale_data]

theorem positivity {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (hc : 0<c)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    0<(run bits model W c k values).1.2 ∧ ∀ j,0<(run bits model W c k values).1.1.read j := by
  rw [data]
  exact GeneralPaperValueRoundingDriver.positive bits model W _ (by unfold scale; exact Nat.mul_pos (Nat.mul_pos hc v.fields_positive) (Nat.two_pow_pos _)) values v hv

theorem denominator {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    scale c n k≤(run bits model W c k values).1.2 ∧ (run bits model W c k values).1.2<scale c n k+n := by
  rw [data]
  exact GeneralPaperValueRoundingDriver.total_bounds bits model W _ values v hv

theorem source_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ) :
    (∑ j,(run bits model W c k values).1.1.read j)=(run bits model W c k values).1.2 := by
  rw [data]
  exact GeneralPaperValueRoundingDriver.sum_weights bits model W _ values

theorem models_data {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W c k values).1=(run false model 1 c k values).1 := by
  rw [data,data]
  exact GeneralPaperValueRoundingDriver.models_data model W _ values v hv

theorem error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (hc : 0<c)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (∑ j,|((run bits model W c k values).1.1.read j:ℚ)/(run bits model W c k values).1.2-v.weight j|)≤
      2*(n:ℚ)/(scale c n k:ℚ) := by
  rw [data]
  exact GeneralPaperValueRoundingDriver.error bits model W _
    (by unfold scale; exact Nat.mul_pos (Nat.mul_pos hc v.fields_positive) (Nat.two_pow_pos _)) values v hv

theorem scaled_error (c n k : ℕ) (hc : 0<c) (hn : 0<n) :
    2*(n:ℚ)/(scale c n k:ℚ)=((1/(2:ℚ)^k)/c)*2 := by
  have hc' : (c:ℚ)≠0 := by exact_mod_cast hc.ne'
  have hn' : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
  unfold scale
  push_cast
  field_simp

theorem original_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (∑ j,|((run bits model W 256 k values).1.1.read j:ℚ)/(run bits model W 256 k values).1.2-v.weight j|)≤
      (1/(2:ℚ)^k)/128 := by
  have h := error bits model W 256 k (by decide) values v hv
  rw [scaled_error 256 n k (by decide) v.fields_positive] at h
  exact h.trans_eq (by ring)

theorem reduced_error {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (∑ j,|((run bits model W 512 k values).1.1.read j:ℚ)/(run bits model W 512 k values).1.2-v.weight j|)≤
      (1/(2:ℚ)^k)/256 := by
  have h := error bits model W 512 k (by decide) values v hv
  rw [scaled_error 512 n k (by decide) v.fields_positive] at h
  exact h.trans_eq (by ring)

theorem reduced_denominator {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run bits model W 512 k values).1.2≤513*n*2^k := by
  have h := (denominator bits model W 512 k values v hv).2.le
  have hp : 1≤2^k := Nat.one_le_two_pow
  unfold scale at h
  nlinarith only [h,Nat.mul_le_mul_left n hp]

theorem reduced_denominator_word {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    binaryWordWidth (run bits model W 512 k values).1.2≤binaryWordWidth n+k+11 := by
  have h := binaryWordWidth_mono (reduced_denominator bits model W k values v hv)
  have h0 := binaryWordWidth_mul (513*n) (2^k)
  have h1 := binaryWordWidth_mul 513 n
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  rw [hp] at h0
  have h513 : binaryWordWidth 513=10 := by decide
  rw [h513] at h1
  omega

theorem equal_entries {n : ℕ} (bits : Bool) (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (i j : Fin n) (he : v.weight i=v.weight j) :
    (run bits model W c k values).1.1.read i=(run bits model W c k values).1.1.read j := by
  rw [data]
  exact GeneralPaperValueRoundingDriver.equal_entries bits model W _ values v hv i j he

theorem bit_work {n : ℕ} (model : RationalCostModel) (W c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W c k values).2≤scaleBitProfile model W c n k+
      13*model.rat (GeneralPaperValueRoundingInputPrice.size (scale c n k) values)+
      512*(n+1)*GeneralPaperSummaryArrayExecution.arrayWord W n+128*W := by
  have hs := scale_bit_work model W c n k
  have hvp := GeneralPaperValueRoundingInputPrice.native_bound model W (scale c n k) values v hv
  unfold run
  dsimp only
  rw [scale_data]
  nlinarith only [hs,hvp]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (c k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run false model 1 c k values).2≤64*(binaryWordWidth k+1)^2+
      GeneralPaperValueRoundingDriver.arithmeticProfile n (scale c n k)+260 := by
  have hs := scale_arithmetic_work model c n k
  have hvp := GeneralPaperValueRoundingDriver.arithmetic_work model (scale c n k) values v hv
  unfold run
  dsimp only
  rw [scale_data]
  nlinarith only [hs,hvp]

end Blotto.GeneralPaperValueRoundingPaperContract
