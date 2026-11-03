import Blotto.GeneralPaperStoredScoreMaximum

/-! Native normalized scalar values are materialized from retained short
integer weights once. The strict-score driver reads this stored array;
the canonical selector is only its erased semantic identity. -/
namespace Blotto.GeneralPaperRetainedFieldValues
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000

structure Values (m : ℕ) where
  values : FixedArrayTable m ℚ
  positive : ∀ j,0<values.read j
  sum_one : (∑ j,values.read j)=1

def selector {m : ℕ} (v : Values m) : RationalFieldSelector m where
  weight := v.values.read
  positive := v.positive
  sum_one := v.sum_one

def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) : Values m×ℕ :=
  let built := GeneralPaperReducedValueArray.identity bits model W Qv weights
  (⟨built.1,GeneralPaperReducedValueArray.identity_positive bits model W Qv hQv weights hp,
    GeneralPaperReducedValueArray.identity_sum bits model W Qv hQv weights hs⟩,built.2+64*address bits W m)

theorem data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) :
    (run bits model W Qv hQv weights hp hs).1.values=FixedArrayTable.ofFn (fun j => (weights.read j:ℚ)/Qv) :=
  GeneralPaperReducedValueArray.identity_data bits model W Qv weights

theorem selector_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) :
    selector (run bits model W Qv hQv weights hp hs).1=GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs := by
  unfold selector GeneralPaperNativeRationalValues.selector
  congr 1
  funext j
  rw [data,FixedArrayTable.read_ofFn]

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) :
    (run false model 1 Qv hQv weights hp hs).2≤79*m+237 := by
  have h := GeneralPaperReducedValueArrayPrice.identity_arithmetic_work model Qv weights
  change (GeneralPaperReducedValueArray.identity false model 1 Qv weights).2+64*1≤_
  omega

theorem bit_work {m : ℕ} (model : RationalCostModel) (W Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : (∑ j,weights.read j)=Qv) :
    (run true model W Qv hQv weights hp hs).2≤m*(3*model.rat (GeneralPaperReducedValueArrayPrice.width Qv 1)+32*arrayWord W m)+
      44*(m+1)*arrayWord W m+model.rat (GeneralPaperReducedValueArrayPrice.width Qv 1)+192*arrayWord W m := by
  have hw : ∀ j,weights.read j≤Qv := by
    rw [←hs]
    intro j
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have h := GeneralPaperReducedValueArrayPrice.identity_bit_work model W Qv weights hw
  unfold run
  dsimp only
  simp only [address,ite_true]
  nlinarith only [h]

end Blotto.GeneralPaperRetainedFieldValues
