import Blotto.GeneralPaperReducedValueArrayPrice

/-! Both reduction branches compose with the literal classifier price.
The field count and common reference word are derived from its actual
returned arrays. Original integer weights are borrowed and retained once. -/
namespace Blotto.GeneralPaperReducedValuesPrice
open GeneralPaperSummaryArrayExecution GeneralPaperReducedValuesDriver
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def post (model : RationalCostModel) (n H A : ℕ) : ℕ :=
  n*(3*model.rat H+64*A)+44*(n+1)*A+7*model.rat H+256*A

theorem absorb (model : RationalCostModel) (n m h H A V : ℕ) (hm : m≤n) (hh : h≤H) (hA : A≤V) :
    m*(3*model.rat h+64*A)+44*(m+1)*A+7*model.rat h+256*A≤post model n H V := by
  have hp := model.monotone hh
  have h0 := Nat.mul_le_mul hm (Nat.add_le_add (Nat.mul_le_mul_left 3 hp) (Nat.mul_le_mul_left 64 hA))
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hm 1)) hA
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) (Nat.mul_le_mul_left 7 hp)) (Nat.mul_le_mul_left 256 hA)

theorem arrayWord_mono (W a b : ℕ) (h : a≤b) : arrayWord W a≤arrayWord W b := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  unfold arrayWord
  omega

theorem sizes {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.heavy.size+
      (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.light.size=n := by
  rw [GeneralPaperLightFieldClassification.data]
  exact GeneralPaperLightFieldScan.sizes bits model W _ Q weights n le_rfl

theorem bit_post {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperReducedValuesDriver.run true model W k Q weights).2≤(GeneralPaperLightFieldClassification.run true model W k Q weights).2+
      post model n (GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k))
        (arrayWord W (2*n+GeneralPaperLightFieldReduction.representatives k)) := by
  have hw : ∀ j,weights.read j≤Q := fun j =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans_eq hs
  have hSizes := sizes true model W k Q weights
  have hR : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2=
      GeneralPaperLightFieldReduction.representatives k :=
    congrArg Prod.snd (GeneralPaperLightFieldClassification.data true model W k Q weights)
  have hL : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound true model W _ Q weights hs n le_rfl
  unfold GeneralPaperReducedValuesDriver.run
  dsimp only
  split_ifs with he
  · have hm : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2≤n := by omega
    have hArray := GeneralPaperReducedValueArrayPrice.replaced_bit_work model W Q
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight weights hw
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy hL
    have hA := arrayWord_mono W (n+(GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2)
      (2*n+GeneralPaperLightFieldReduction.representatives k) (by omega)
    have hAbs := absorb model n
      ((GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2)
      (GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2)
      (GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2)
      (arrayWord W (n+(GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2))
      (arrayWord W (2*n+GeneralPaperLightFieldReduction.representatives k)) hm (le_refl _) hA
    rw [hR] at hArray hAbs ⊢
    simp only [GeneralPaperSourceRowsExecution.address,ite_true]
    omega
  · have hArray := GeneralPaperReducedValueArrayPrice.identity_bit_work model W Q weights hw
    have hH : GeneralPaperReducedValueArrayPrice.width Q 1≤
        GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k) := by
      have h : binaryWordWidth 1≤binaryWordWidth (GeneralPaperLightFieldReduction.representatives k) :=
        binaryWordWidth_mono (Nat.succ_le_of_lt (GeneralPaperLightFieldReduction.representatives_positive k))
      unfold GeneralPaperReducedValueArrayPrice.width
      omega
    have hA := arrayWord_mono W n (2*n+GeneralPaperLightFieldReduction.representatives k) (by omega)
    have hA' := arrayWord_mono W (n+n) (2*n+GeneralPaperLightFieldReduction.representatives k) (by omega)
    have hp := model.monotone hH
    have hCallback := Nat.mul_le_mul_left n (Nat.add_le_add (Nat.mul_le_mul_left 3 hp) (Nat.mul_le_mul_left 32 hA))
    have hOver := Nat.mul_le_mul_left (44*(n+1)) hA
    have hBound := hArray.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hCallback hOver) hp) (Nat.mul_le_mul_left 128 hA))
    simp only [GeneralPaperSourceRowsExecution.address,ite_true]
    have hExtra := Nat.mul_le_mul_left 128 hA'
    unfold post
    nlinarith only [hBound,hExtra,Nat.zero_le (n*arrayWord W (2*n+GeneralPaperLightFieldReduction.representatives k))]

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (GeneralPaperReducedValuesDriver.run false model 1 k Q weights).2≤128*(binaryWordWidth k+1)^2+210*n+763 := by
  have hClass := GeneralPaperLightFieldClassification.arithmetic_work model k Q weights
  have hSizes := sizes false model 1 k Q weights
  unfold GeneralPaperReducedValuesDriver.run
  dsimp only
  simp only [GeneralPaperSourceRowsExecution.address,Bool.false_eq_true,ite_false,Nat.mul_one]
  split_ifs with he
  · have hm : (GeneralPaperLightFieldClassification.run false model 1 k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run false model 1 k Q weights).1.2≤n := by omega
    have hArray := GeneralPaperReducedValueArrayPrice.replaced_arithmetic_work model Q
      (GeneralPaperLightFieldClassification.run false model 1 k Q weights).1.2
      (GeneralPaperLightFieldClassification.run false model 1 k Q weights).1.1.lightWeight weights
      (GeneralPaperLightFieldClassification.run false model 1 k Q weights).1.1.heavy
    nlinarith only [hClass,hArray,hm]
  · have hArray := GeneralPaperReducedValueArrayPrice.identity_arithmetic_work model Q weights
    nlinarith only [hClass,hArray]

end Blotto.GeneralPaperReducedValuesPrice
