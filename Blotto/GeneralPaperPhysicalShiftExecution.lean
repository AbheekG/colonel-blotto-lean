import Blotto.GeneralPaperResponsePhysicalHeights
import Blotto.GeneralPaperPhysicalPowerArithmetic

/-! Construct the paper's shared physical shift once by native repeated
squaring and literal products, casts and rational division. Exponent/index
words are analysis only; the program never inspects a binary encoding. -/
namespace Blotto.GeneralPaperPhysicalShiftExecution
open GeneralPaperTagBudgetTransfer GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def naturalWork (price : ℕ → ℕ) (m qbar power : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) m 2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 4 m+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) (4*m) qbar+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) (4*m*qbar) power

def run (bits : Bool) (model : RationalCostModel) (W m qbar C : ℕ) : ℚ × ℕ :=
  let A := address bits W (m+3)
  let power := if bits then
    let priced := GeneralPaperNatPowerBits.run model.rat A C (m+2)
    (priced.1.power,priced.2)
    else GeneralPaperPhysicalPowerArithmetic.run C (m+2)
  let denominator := 4*m*qbar*power.1
  let den : ℚ := denominator
  (1/den,power.2+naturalWork (primitive bits model) m qbar power.1+
    primitive bits model (rationalWordWidth den)+primitive bits model (rationalWordWidth (1:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary (primitive bits model) (fun a b => a/b) 1 den+128*A)

theorem data (bits : Bool) (model : RationalCostModel) (W m qbar C : ℕ) :
    (run bits model W m qbar C).1=shift m qbar C := by
  cases bits with
  | false =>
    unfold run
    simp only [Bool.false_eq_true,ite_false]
    rw [GeneralPaperPhysicalPowerArithmetic.data]
    rfl
  | true =>
    unfold run
    simp only [ite_true]
    rw [GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data C (m+2)).1]
    rfl

theorem height (bits : Bool) (model : RationalCostModel) (W m qbar C : ℕ) :
    RationalHeight (run bits model W m qbar C).1 (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar C) := by
  rw [data]
  exact GeneralPaperResponsePhysicalHeights.shift_height m qbar C

def natWidth (m qbar C : ℕ) : ℕ :=
  64+8*binaryWordWidth (m+3)+8*binaryWordWidth qbar+8*((m+3)*binaryWordWidth C)
def width (m qbar C : ℕ) : ℕ := 4*natWidth m qbar C

theorem native_words (m qbar C n : ℕ)
    (hn : n∈[4,m,qbar,m+2,C^(m+2),4*m,4*m*qbar,shiftDenominator m qbar C]) :
    1+binaryWordWidth n≤natWidth m qbar C := by
  have hm := binaryWordWidth_mono (show m≤m+3 by omega)
  have he := binaryWordWidth_mono (show m+2≤m+3 by omega)
  have hp := GeneralPaperNatPowerOperands.power_width C (m+2)
  have hp' := Nat.mul_le_mul_right (binaryWordWidth C) (show m+2≤m+3 by omega)
  have h0 := binaryWordWidth_mul 4 m
  have h1 := binaryWordWidth_mul (4*m) qbar
  have h2 := binaryWordWidth_mul (4*m*qbar) (C^(m+2))
  rw [show binaryWordWidth 4=3 by decide] at h0
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with hn|hn
  · subst n
    unfold natWidth
    rw [show binaryWordWidth 4=3 by decide]
    omega
  · rcases hn with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      dsimp only [natWidth,shiftDenominator] <;> omega

theorem power_width (m qbar C : ℕ) : GeneralPaperNatPowerOperands.width C (m+2)≤width m qbar C := by
  have hm := binaryWordWidth_mono (show m+2≤m+3 by omega)
  have hp := Nat.mul_le_mul_right (binaryWordWidth C) (show m+2≤m+3 by omega)
  have hC := Nat.mul_le_mul_right (binaryWordWidth C) (show 1≤m+3 by omega)
  unfold GeneralPaperNatPowerOperands.width width natWidth
  omega

theorem rational_words (m qbar C : ℕ) :
    rationalWordWidth (shiftDenominator m qbar C:ℚ)≤width m qbar C ∧
    rationalWordWidth (shift m qbar C)≤width m qbar C ∧ rationalWordWidth (1:ℚ)≤width m qbar C := by
  have hn := native_words m qbar C (shiftDenominator m qbar C) (by simp)
  have hd := GeneralPaperBasisDivideBits.nat_height (shiftDenominator m qbar C)
  have hdw := rationalWordWidth_of_height hd
  have hsw := rationalWordWidth_of_height hd.inv
  rw [show rationalWordWidth (1:ℚ)=3 by decide]
  simp only [shift,one_div]
  unfold width
  omega

theorem natural_work (model : RationalCostModel) (m qbar C : ℕ) :
    naturalWork model.rat m qbar (C^(m+2))≤8*model.rat (width m qbar C) := by
  have hw (n : ℕ) (hn : n∈[4,m,qbar,m+2,C^(m+2),4*m,4*m*qbar,shiftDenominator m qbar C]) :
      1+binaryWordWidth n≤width m qbar C :=
    (native_words m qbar C n hn).trans (by unfold width; omega)
  have htwo : 1+binaryWordWidth 2≤width m qbar C := by
    rw [show binaryWordWidth 2=2 by decide]; unfold width natWidth; omega
  have h0 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
    m 2 (width m qbar C) (hw _ (by simp)) htwo (hw _ (by simp))
  have h1 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b)
    4 m (width m qbar C) (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp))
  have h2 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b)
    (4*m) qbar (width m qbar C) (hw _ (by simp)) (hw _ (by simp)) (hw _ (by simp))
  have h3 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a*b)
    (4*m*qbar) (C^(m+2)) (width m qbar C) (hw _ (by simp)) (hw _ (by simp))
    (hw (shiftDenominator m qbar C) (by simp))
  unfold naturalWork
  omega

def bitProfile (model : RationalCostModel) (W m qbar C : ℕ) : ℕ :=
  64*(binaryWordWidth (m+2)+1)*(arrayWord W (m+3)+model.rat (width m qbar C))+
    16*model.rat (width m qbar C)+128*arrayWord W (m+3)

theorem bit_work (model : RationalCostModel) (W m qbar C : ℕ) (hC : 0<C) :
    (run true model W m qbar C).2≤bitProfile model W m qbar C := by
  have hp := GeneralPaperNatPowerBits.work model.rat model.monotone (arrayWord W (m+3)) C (m+2) hC
  have hw := model.monotone (power_width m qbar C)
  have hp' := hp.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hw _))
  have hn := natural_work model m qbar C
  obtain ⟨hd,hs,hOne⟩ := rational_words m qbar C
  have hd' := model.monotone hd
  have ho' := model.monotone hOne
  have hdiv := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b)
    1 (shiftDenominator m qbar C:ℚ) (width m qbar C) hOne hd hs
  unfold run bitProfile
  dsimp only
  simp only [primitive,address,ite_true]
  rw [GeneralPaperNatPowerBits.data,(GeneralPaperNatPower.data C (m+2)).1]
  change (GeneralPaperNatPowerBits.run model.rat (arrayWord W (m+3)) C (m+2)).2+
    naturalWork model.rat m qbar (C^(m+2))+model.rat (rationalWordWidth (shiftDenominator m qbar C:ℚ))+
    model.rat (rationalWordWidth (1:ℚ))+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) 1 (shiftDenominator m qbar C:ℚ)+
    128*arrayWord W (m+3)≤_
  omega

theorem arithmetic_work (model : RationalCostModel) (m qbar C : ℕ) :
    (run false model 1 m qbar C).2≤64*(binaryWordWidth (m+2)+1)^2+140 := by
  have hp := GeneralPaperPhysicalPowerArithmetic.work C (m+2)
  unfold run
  dsimp only
  simp only [primitive,address,Bool.false_eq_true,ite_false,naturalWork,
    GeneralPaperNaturalPrimitivePrice.binary,GeneralPaperRationalPrimitivePrice.binary]
  nlinarith only [hp]

end Blotto.GeneralPaperPhysicalShiftExecution
