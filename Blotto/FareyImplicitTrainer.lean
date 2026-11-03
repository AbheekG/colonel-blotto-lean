import Blotto.FareySourceUniverses
import Blotto.SourceBoundedImplicitTraining

/-! Actual Farey rank decoders instantiate the compact raw trainer. Monotonicity,
zero bids and source code widths are derived, with arbitrary nonnegative field
scales and original labelled duplicate codes. Continuous input reduction and
full decoder/preparation costs remain separate. -/

namespace Blotto.FareyImplicitTrainer
open scoped BigOperators
open Farey

def bids {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) :
    (field : Fin m) → Fin (rankCap spec.order + 1) → ℚ :=
  fun field code => scale field * spec.decode code.val

theorem bids_nonnegative {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hScale : ∀ field, 0 ≤ scale field)
    (field : Fin m) (code : Fin (rankCap spec.order + 1)) : 0 ≤ bids spec scale field code :=
  mul_nonneg (hScale field) (decode_nonnegative spec code.val)

theorem zero_feasible {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (budget : ℚ) (hb : 0 ≤ budget) :
    SparseMW.productResource (bids spec scale) (fun _ => 0) ≤ budget := by
  simpa only [SparseMW.productResource,bids,Fin.val_zero,decode_zero,mul_zero,Finset.sum_const_zero] using hb

def create {m : ℕ} (first second : RankUniverse) (scaleA scaleB : Fin m → ℚ)
    (hA : ∀ field, 0 ≤ scaleA field) (hB : ∀ field, 0 ≤ scaleB field)
    (budgetA budgetB : ℚ) (hbA : 0 ≤ budgetA) (hbB : 0 ≤ budgetB) (values : RationalFieldSelector m)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1/4) (htheta : 0 < theta ∧ theta ≤ 1/2) : ProductSecurityTrainer m where
  sizesA := fun _ => rankCap first.order + 1
  sizesB := fun _ => rankCap second.order + 1
  bidsA := bids first scaleA
  bidsB := bids second scaleB
  bidsA_nonnegative := bids_nonnegative first scaleA hA
  bidsB_nonnegative := bids_nonnegative second scaleB hB
  budgetA := budgetA
  budgetB := budgetB
  fallbackA := fun _ => 0
  fallbackB := fun _ => 0
  fallbackA_feasible := zero_feasible first scaleA budgetA hbA
  fallbackB_feasible := zero_feasible second scaleB budgetB hbB
  values := values
  eta := eta
  theta := theta
  eta_unit := heta
  theta_unit := htheta

theorem decoder_ordered {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (hScale : ∀ field, 0 ≤ scale field)
    (field : Fin m) : MonotoneResourceCuts.MonotoneDecode (rankCap spec.order)
      (ProductSecurityTrainer.bidDecoder (bids spec scale) field) := by
  intro first second hOrder hSecond
  have hFirst : first < rankCap spec.order + 1 := by omega
  have hLast : second < rankCap spec.order + 1 := by omega
  simp only [ProductSecurityTrainer.bidDecoder,hFirst,hLast,dite_true,bids]
  exact mul_le_mul_of_nonneg_left (decode_mono spec first second hOrder hSecond) (hScale field)

theorem decoder_zero {m : ℕ} (spec : RankUniverse) (scale : Fin m → ℚ) (field : Fin m) :
    ProductSecurityTrainer.bidDecoder (bids spec scale) field 0 = 0 := by
  have h : 0 < rankCap spec.order + 1 := by omega
  simp only [ProductSecurityTrainer.bidDecoder,h,dite_true,bids,decode_zero,mul_zero]

def config {m : ℕ} (first second : RankUniverse) (scaleA scaleB : Fin m → ℚ)
    (hA : ∀ field, 0 ≤ scaleA field) (hB : ∀ field, 0 ≤ scaleB field)
    (budgetA budgetB : ℚ) (hbA : 0 ≤ budgetA) (hbB : 0 ≤ budgetB) (values : RationalFieldSelector m)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1/4) (htheta : 0 < theta ∧ theta ≤ 1/2) :
    (create first second scaleA scaleB hA hB budgetA budgetB hbA hbB values eta theta heta htheta).ImplicitCodeConfig where
  capsA := fun _ => rankCap first.order
  capsB := fun _ => rankCap second.order
  sizesA := rfl
  sizesB := rfl
  orderedA := decoder_ordered first scaleA hA
  orderedB := decoder_ordered second scaleB hB
  zeroA := decoder_zero first scaleA
  zeroB := decoder_zero second scaleB

theorem config_widths {m : ℕ} (first second : RankUniverse) (scaleA scaleB : Fin m → ℚ)
    (hA : ∀ field, 0 ≤ scaleA field) (hB : ∀ field, 0 ≤ scaleB field)
    (budgetA budgetB : ℚ) (hbA : 0 ≤ budgetA) (hbB : 0 ≤ budgetB) (values : RationalFieldSelector m)
    (eta theta : ℚ) (heta : 0 < eta ∧ eta ≤ 1/4) (htheta : 0 < theta ∧ theta ≤ 1/2) :
    (∀ field, binaryWordWidth ((config first second scaleA scaleB hA hB budgetA budgetB hbA hbB values eta theta heta htheta).capsA field + 1)
      ≤ 6 + 2 * binaryWordWidth first.order) ∧
    (∀ field, binaryWordWidth ((config first second scaleA scaleB hA hB budgetA budgetB hbA hbB values eta theta heta htheta).capsB field + 1)
      ≤ 6 + 2 * binaryWordWidth second.order) :=
  ⟨fun _ => rankCap_word_bound first.order first.order_positive,fun _ => rankCap_word_bound second.order second.order_positive⟩

end Blotto.FareyImplicitTrainer
