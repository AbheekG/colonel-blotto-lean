import Blotto.GeneralPaperLightFieldScanContract

/-! Complete native classifier: construct its threshold and representative
count once, scan the retained original integer weights once and return both
the index arrays and the exact light integer mass. Real/bit data agree.
This is still one phase of the final input/reduction/lifting driver. -/
namespace Blotto.GeneralPaperLightFieldClassification
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (GeneralPaperLightFieldScan.State n × ℕ) × ℕ :=
  let threshold := GeneralPaperValueRoundingPaperContract.scaleRun bits model W 10 1 k
  let scanned := GeneralPaperLightFieldScan.scan bits model W threshold.1 Q weights n le_rfl
  let reps := GeneralPaperValueRoundingPaperContract.scaleRun bits model W 8 1 k
  ((scanned.1,reps.1),threshold.2+scanned.2+reps.2+128*address bits W n)

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run bits model W k Q weights).1=
      ((GeneralPaperLightFieldScan.scan bits model W (GeneralPaperLightFieldScanContract.multiplier k) Q weights n le_rfl).1,
        GeneralPaperLightFieldReduction.representatives k) := by
  unfold run
  simp only [GeneralPaperValueRoundingPaperContract.scale_data,GeneralPaperValueRoundingPaperContract.scale,
    Nat.mul_one,GeneralPaperLightFieldScanContract.multiplier,GeneralPaperLightFieldReduction.representatives]

theorem models_data {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run true model W k Q weights).1=(run false model 1 k Q weights).1 := by
  rw [data,data,GeneralPaperLightFieldScan.models_data]

theorem bit_work {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    (run true model W k Q weights).2≤
      GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 10 1 k+
      GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 8 1 k+
      n*(5*model.rat (1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude
        (GeneralPaperLightFieldScanContract.multiplier k) Q))+128*arrayWord W n)+192*arrayWord W n := by
  have h10 := GeneralPaperValueRoundingPaperContract.scale_bit_work model W 10 1 k
  have h8 := GeneralPaperValueRoundingPaperContract.scale_bit_work model W 8 1 k
  have hScan := GeneralPaperLightFieldScanPrice.bit_work model W (GeneralPaperLightFieldScanContract.multiplier k) Q weights hs n le_rfl
  unfold run
  dsimp only
  rw [GeneralPaperValueRoundingPaperContract.scale_data]
  simp only [GeneralPaperValueRoundingPaperContract.scale,Nat.mul_one,address,ite_true]
  unfold GeneralPaperLightFieldScanContract.multiplier at hScan ⊢
  nlinarith only [h10,h8,hScan]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (run false model 1 k Q weights).2≤128*(binaryWordWidth k+1)^2+130*n+456 := by
  have h10 := GeneralPaperValueRoundingPaperContract.scale_arithmetic_work model 10 1 k
  have h8 := GeneralPaperValueRoundingPaperContract.scale_arithmetic_work model 8 1 k
  have hScan := GeneralPaperLightFieldScanPrice.arithmetic_work model (GeneralPaperLightFieldScanContract.multiplier k) Q weights n le_rfl
  unfold run
  dsimp only
  rw [GeneralPaperValueRoundingPaperContract.scale_data]
  simp only [GeneralPaperValueRoundingPaperContract.scale,Nat.mul_one,address,Bool.false_eq_true,ite_false]
  unfold GeneralPaperLightFieldScanContract.multiplier at hScan
  nlinarith only [h10,h8,hScan]

theorem reduced_count_bounds {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    let returned := (run bits model W k Q weights).1
    let m := returned.1.heavy.size+min returned.1.light.size returned.2
    0<m ∧ m≤n ∧ m<18*2^k := by
  rw [data]
  exact GeneralPaperLightFieldScanContract.reduced_count_bounds bits model W Q k hQ weights hp hs

theorem light_entry {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (j : Fin n) (hj : j∈(run bits model W k Q weights).1.1.light) :
    (weights.read j:ℚ)/Q≤GeneralPaperLightFieldReduction.accuracy k/10 := by
  rw [data] at hj
  exact (GeneralPaperLightFieldScanContract.threshold (weights.read j) Q k hQ).mpr
    ((GeneralPaperLightFieldScan.light_mem bits model W _ Q weights n le_rfl j).mp hj).2

theorem heavy_entry {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (j : Fin n) (hj : j∈(run bits model W k Q weights).1.1.heavy) :
    GeneralPaperLightFieldReduction.accuracy k/10<(weights.read j:ℚ)/Q := by
  rw [data] at hj
  have h := ((GeneralPaperLightFieldScan.heavy_mem bits model W _ Q weights n le_rfl j).mp hj).2
  exact lt_of_not_ge (fun hc => Nat.not_lt_of_ge ((GeneralPaperLightFieldScanContract.threshold (weights.read j) Q k hQ).mp hc) h)

theorem light_mass {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (hQ : 0<Q)
    (weights : FixedArrayTable n ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Q) :
    ((run bits model W k Q weights).1.1.lightWeight:ℚ)/Q=
      GeneralPaperLightFieldReduction.mass (GeneralPaperNativeRationalValues.selector Q hQ weights hp hs) k := by
  rw [data]
  exact GeneralPaperLightFieldScanContract.light_mass bits model W Q k hQ weights hp hs

theorem original_rounded_count {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let first := (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1
    let classified := (run bits model W k first.2 first.1).1
    let m := classified.1.heavy.size+min classified.1.light.size classified.2
    0<m ∧ m≤n ∧ m<18*2^k := by
  dsimp only
  have hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv
  exact reduced_count_bounds bits model W k _ hp.1 _ hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)

end Blotto.GeneralPaperLightFieldClassification
