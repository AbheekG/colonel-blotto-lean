import Blotto.GeneralPaperOriginalSourceValuePreparation

/-! Actual two-round original value preparation prices. Long original
rational lengths occur only in the first aggregate input price; reduced
values have short widths derived from the retained integer construction. -/
namespace Blotto.GeneralPaperOriginalSourceValuePrice
open GeneralPaperOriginalSourceValuePreparation GeneralPaperSummaryArrayExecution
open GeneralPaperSourceRowsExecution
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem reduced_values_width {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ)
    (weights : FixedArrayTable n ℕ) (hs : ∑ j,weights.read j=Q) :
    ∀ j,rationalWordWidth ((GeneralPaperReducedValuesDriver.run bits model W k Q weights).1.values.read j)≤
      GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k) := by
  have hw (j : Fin n) : weights.read j≤Q :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq hs
  have hL : (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound bits model W _ Q weights hs n le_rfl
  have hR : (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.2=
      GeneralPaperLightFieldReduction.representatives k :=
    congrArg Prod.snd (GeneralPaperLightFieldClassification.data bits model W k Q weights)
  let Good (o : GeneralPaperReducedValuesDriver.Output n) : Prop :=
    ∀ j,rationalWordWidth (o.values.read j)≤GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k)
  change Good _
  rw [GeneralPaperReducedValuesDriver.data,GeneralPaperReducedValuesDriver.specification]
  split
  · dsimp only [Good]
    intro j
    rw [FixedArrayTable.read_ofFn]
    split_ifs
    · exact GeneralPaperReducedValueArrayPrice.ratio_width _ Q _ (hw _)
    · rw [←hR]
      exact GeneralPaperReducedValueArrayPrice.representative_width _ Q _ hL
  · dsimp only [Good]
    intro j
    rw [FixedArrayTable.read_ofFn]
    exact GeneralPaperReducedValueArrayPrice.ratio_width _ Q _ (hw j)

def reducedWidth (n k : ℕ) : ℕ := 512*(binaryWordWidth n+k+1)

theorem original_reduced_width {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    ∀ j,rationalWordWidth ((GeneralPaperOriginalValueReduction.run bits model W k values).1.values.read j)≤reducedWidth n k := by
  intro j
  have h := reduced_values_width bits model W k
    (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.1
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values) j
  have hWidth := GeneralPaperOriginalValueReductionPrice.returned_width bits model W k values v hv
  rw [(GeneralPaperOriginalValueReduction.retained bits model W k values).2] at hWidth
  exact h.trans hWidth

def secondSize (n k : ℕ) : ℕ :=
  8*n*reducedWidth n k+n*(33+9*binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale 512 n k+n))

theorem second_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k values).1
    GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 512 o.m k) o.values≤secondSize n k := by
  dsimp only
  have hm := (GeneralPaperOriginalValueReduction.count_bounds bits model W k values v hv).2.1
  have hwidth := original_reduced_width bits model W k values v hv
  have hsum : GeneralPaperValueRoundingInputPrice.inputSize (GeneralPaperOriginalValueReduction.run bits model W k values).1.values≤
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.m*reducedWidth n k := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hwidth j)
    simpa only [GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h
  unfold GeneralPaperValueRoundingInputPrice.size secondSize GeneralPaperValueRoundingPaperContract.scale
  calc
    _≤8*((GeneralPaperOriginalValueReduction.run bits model W k values).1.m*reducedWidth n k)+
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.m*
        (33+9*binaryWordWidth (512*(GeneralPaperOriginalValueReduction.run bits model W k values).1.m*2^k+
          (GeneralPaperOriginalValueReduction.run bits model W k values).1.m)) := Nat.add_le_add_right (Nat.mul_le_mul_left 8 hsum) _
    _≤8*(n*reducedWidth n k)+n*(33+9*binaryWordWidth (512*n*2^k+n)) := by gcongr
    _= _ := by ring

def scaleWidth (c n k : ℕ) : ℕ := 64+4*(binaryWordWidth c+binaryWordWidth n+k+1)
def scalePrice (model : RationalCostModel) (W c n k : ℕ) : ℕ :=
  64*(binaryWordWidth k+1)*(W+model.rat (GeneralPaperNatPowerOperands.width 2 k))+
    4*model.rat (scaleWidth c n k)+128*W

theorem scale_price (model : RationalCostModel) (W c m n k : ℕ) (hm : m≤n) :
    GeneralPaperValueRoundingPaperContract.scaleBitProfile model W c m k≤scalePrice model W c n k := by
  have hn := binaryWordWidth_mono hm
  have hcm := binaryWordWidth_mul c m
  have hp : binaryWordWidth (2^k)=k+1 := by simp only [binaryWordWidth,Nat.log2_two_pow]
  have hprod := binaryWordWidth_mul (c*m) (2^k)
  have h1 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) c m (scaleWidth c n k)
    (by unfold scaleWidth;omega) (by unfold scaleWidth;omega) (by unfold scaleWidth;omega)
  have h2 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b) (c*m) (2^k) (scaleWidth c n k)
    (by unfold scaleWidth;omega) (by unfold scaleWidth;omega) (by unfold scaleWidth;omega)
  unfold GeneralPaperValueRoundingPaperContract.scaleBitProfile scalePrice
  omega

def arithmeticPrice (n k : ℕ) : ℕ :=
  256*(binaryWordWidth k+1)^2+
    GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 256 n k)+
    GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 512 n k)+210*n+1539

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run false model 1 k values v hv).2≤arithmeticPrice n k := by
  have hFirst := GeneralPaperOriginalValueReduction.arithmetic_work model k values v hv
  have hSecond := GeneralPaperValueRoundingPaperContract.arithmetic_work model 512 k
    (GeneralPaperOriginalValueReduction.run false model 1 k values).1.values
    (GeneralPaperOriginalValueReduction.selector false model 1 k values v hv) (fun _ => rfl)
  have hm := (GeneralPaperOriginalValueReduction.count_bounds false model 1 k values v hv).2.1
  have hMono : GeneralPaperValueRoundingDriver.arithmeticProfile
      (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m
      (GeneralPaperValueRoundingPaperContract.scale 512 (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k)≤
      GeneralPaperValueRoundingDriver.arithmeticProfile n (GeneralPaperValueRoundingPaperContract.scale 512 n k) := by
    unfold GeneralPaperValueRoundingDriver.arithmeticProfile GeneralPaperValueRoundArray.arithmeticProfile
      GeneralPaperValueRoundingPaperContract.scale
    gcongr
  dsimp only [GeneralPaperOriginalSourceValuePreparation.run]
  simp only [address,Bool.false_eq_true,ite_false,Nat.mul_one]
  unfold arithmeticPrice
  omega

noncomputable def bitPrice {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  GeneralPaperOriginalValueReductionPrice.profile model W k values+scalePrice model W 512 n k+
    13*model.rat (secondSize n k)+512*(n+1)*arrayWord W n+128*W+128*arrayWord W (2*n)

theorem bit_work {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (run true model W k values v hv).2≤bitPrice model W k values := by
  have hFirst := GeneralPaperOriginalValueReductionPrice.bit_work model W k values v hv
  have hSecond := GeneralPaperValueRoundingPaperContract.bit_work model W 512 k
    (GeneralPaperOriginalValueReduction.run true model W k values).1.values
    (GeneralPaperOriginalValueReduction.selector true model W k values v hv) (fun _ => rfl)
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  have hScale := scale_price model W 512 _ n k hm
  have hSize := model.monotone (second_size true model W k values v hv)
  have hArray := GeneralPaperReducedValuesPrice.arrayWord_mono W _ n hm
  have hFields := Nat.mul_le_mul (Nat.add_le_add_right hm 1) hArray
  have hParent := Nat.mul_le_mul_left 128 (GeneralPaperReducedValuesPrice.arrayWord_mono W
    (n+(GeneralPaperOriginalValueReduction.run true model W k values).1.m) (2*n) (by omega))
  dsimp only [GeneralPaperOriginalSourceValuePreparation.run]
  simp only [address,ite_true]
  unfold bitPrice
  nlinarith only [hFirst,hSecond,hScale,hSize,hFields,hParent]

end Blotto.GeneralPaperOriginalSourceValuePrice
