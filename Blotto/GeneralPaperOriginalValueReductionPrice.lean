import Blotto.GeneralPaperOriginalValueReduction

/-! Full original-round/classify/reduce bit price, with additive original
value lengths from the already checked first-round input price. All later
scalar widths depend only on short returned integer weights and k. -/
namespace Blotto.GeneralPaperOriginalValueReductionPrice
open GeneralPaperSummaryArrayExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

noncomputable def profile {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  let Q := (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
  let R := GeneralPaperLightFieldReduction.representatives k
  GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 256 n k+
    13*model.rat (GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 256 n k) values)+
    512*(n+1)*arrayWord W n+128*W+
    GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 10 1 k+
    GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 8 1 k+
    n*(5*model.rat (1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude
      (GeneralPaperLightFieldScanContract.multiplier k) Q))+128*arrayWord W n)+192*arrayWord W n+
    GeneralPaperReducedValuesPrice.post model n (GeneralPaperReducedValueArrayPrice.width Q R) (arrayWord W (2*n+R))+
    128*arrayWord W (2*n)

theorem bit_work {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalValueReduction.run true model W k values).2≤profile model W k values := by
  have hFirst := GeneralPaperValueRoundingPaperContract.bit_work model W 256 k values v hv
  have hs := GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values
  have hClass := GeneralPaperLightFieldClassification.bit_work model W k
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.1 hs
  have hReduced := GeneralPaperReducedValuesPrice.bit_post model W k
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.1 hs
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  rw [GeneralPaperOriginalValueReduction.data] at hm
  have hFrame := Nat.mul_le_mul_left 128 (GeneralPaperReducedValuesPrice.arrayWord_mono W
    (n+(GeneralPaperReducedValuesDriver.run true model W k
      (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
      (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.1).1.m) (2*n) (by omega))
  unfold GeneralPaperOriginalValueReduction.run profile
  dsimp only
  simp only [GeneralPaperSourceRowsExecution.address,ite_true]
  nlinarith only [hFirst,hClass,hReduced,hFrame]

theorem representatives_word (k : ℕ) : binaryWordWidth (GeneralPaperLightFieldReduction.representatives k)=k+4 := by
  have he : GeneralPaperLightFieldReduction.representatives k=2^(k+3) := by
    unfold GeneralPaperLightFieldReduction.representatives
    rw [pow_add]
    norm_num
    omega
  rw [he]
  simp only [binaryWordWidth,Nat.log2_two_pow]

theorem returned_width {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    GeneralPaperReducedValueArrayPrice.width (GeneralPaperOriginalValueReduction.run bits model W k values).1.denominator
      (GeneralPaperLightFieldReduction.representatives k)≤512*(binaryWordWidth n+k+1) := by
  have h := GeneralPaperOriginalValueReduction.denominator_word bits model W k values v hv
  have hr := representatives_word k
  unfold GeneralPaperReducedValueArrayPrice.width
  rw [hr]
  omega

end Blotto.GeneralPaperOriginalValueReductionPrice
