import Blotto.GeneralPaperEpochNumeratorEnvelope

/-! Eight local level arrays use these single indexed addition loops.
The source parameter record derives every addition word; the data agree
with the native level updater. Global references remain explicit in W.
-/
namespace Blotto.GeneralPaperEpochLevelPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def element {n : ℕ} (price : ℕ → ℕ) (W : ℕ) (current delta : FixedArrayTable n ℕ) (r : Fin n) : ℕ × ℕ :=
  let before := current.read r
  let change := delta.read r
  (before+change,GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) before change+32*W)

def run {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (current delta : FixedArrayTable n ℕ) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W n else W) (element price W current delta)

theorem data {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (current delta : FixedArrayTable n ℕ) :
    (run bits index price W current delta).1=(GeneralPaperEpochLevelArray.advance current delta).1 := by
  simp only [run,GeneralPaperEpochLevelArray.advance,PaperIndexedArrayConstruction.run_data,element]

theorem operand_word (m lambda k Qv : ℕ) :
    1+binaryWordWidth (GeneralPaperPowerPrecision.levelBound lambda k+
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator)≤
        GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  let M := GeneralPaperSourcePreparationSizes.measure m lambda k Qv
  let G := GeneralPaperPowerPrecision.levelBound lambda k
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  have hg := (GeneralPaperSourcePreparationSizes.sizes m lambda k Qv).columnsTarget
  change binaryWordWidth (G+1)≤32*M at hg
  have hgm := binaryWordWidth_mono (show G≤G+1 by omega)
  have hm := GeneralPaperNatPowerOperands.power_width 2 (29+k)
  have hTwo : binaryWordWidth 2=2 := by decide
  rw [hTwo,←(GeneralPaperSourceParameters.data k).2.2.2.2.1] at hm
  change binaryWordWidth mesh≤1+(29+k)*2 at hm
  have h8 := binaryWordWidth_mul 8 mesh
  have hs := GeneralPaperRayOperandWidthEnvelope.word_add G (8*mesh)
  have hEight : binaryWordWidth 8=4 := by decide
  have hk := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).1
  have hM := (GeneralPaperSourcePreparationEnvelope.base m lambda k Qv).2
  change k+128≤M at hk
  change 128≤M at hM
  change 1+binaryWordWidth (G+8*mesh)≤1048576*M
  omega

def profile (price : ℕ → ℕ) (W m lambda k Qv n : ℕ) : ℕ :=
  n*(2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+32*W)+44*(n+1)*arrayWord W n

def arithmeticProfile (n : ℕ) : ℕ := n*34+44*(n+1)

theorem element_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (current delta : FixedArrayTable n ℕ) (r : Fin n)
    (hCurrent : current.read r≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hDelta : delta.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (element price W current delta r).2≤2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+32*W := by
  have h := (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a+b) (current.read r) (delta.read r)
    (GeneralPaperPowerPrecision.levelBound lambda k+8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (by omega) (by omega) (Nat.add_le_add hCurrent hDelta)).trans
      (Nat.mul_le_mul_left 2 (hMono (operand_word m lambda k Qv)))
  exact Nat.add_le_add_right h _

theorem bit_work {n : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda k Qv : ℕ)
    (current delta : FixedArrayTable n ℕ)
    (hCurrent : ∀ r,current.read r≤GeneralPaperPowerPrecision.levelBound lambda k)
    (hDelta : ∀ r,delta.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run true (fun w => w) price W current delta).2≤profile price W m lambda k Qv n :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) _ (element price W current delta)
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n)
    (fun r => element_work price hMono W m lambda k Qv current delta r (hCurrent r) (hDelta r))

theorem arithmetic_work {n : ℕ} (current delta : FixedArrayTable n ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 current delta).2≤arithmeticProfile n := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 34 (element (fun _ => 1) 1 current delta)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile] using h

theorem same_data {n : ℕ} (price : ℕ → ℕ) (W : ℕ) (current delta : FixedArrayTable n ℕ) :
    (run true (fun w => w) price W current delta).1=(run false (fun _ => 1) (fun _ => 1) 1 current delta).1 := by rw [data,data]

end Blotto.GeneralPaperEpochLevelPrice
