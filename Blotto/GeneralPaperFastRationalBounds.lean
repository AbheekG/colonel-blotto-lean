import Blotto.GeneralPaperFastRationalModel

/-! Fast primitive bounds retain the sum of actual operand widths. A common
logarithmic factor can be extracted from a finite family without charging
the longest operand at every occurrence. Primitive price-word bounds will
also be used in the source's erased address calibration. -/
namespace Blotto.GeneralPaperFastRationalBounds
open GeneralPaperFastRationalModel
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem charge_at_cap (C d w cap : ℕ) (hw : w≤cap) :
    charge C d w≤C*w*logFactor d cap :=
  Nat.mul_le_mul_left _ (factor_monotone d hw)

theorem primitive_at_cap {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (w cap : ℕ) (hw : w≤cap) : model.rat w≤C*w*logFactor d cap :=
  (hg w).trans (charge_at_cap C d w cap hw)

theorem weighted_sum {ι : Type*} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (indices : Finset ι) (weight width : ι → ℕ) (cap : ℕ) (hw : ∀ i∈indices,width i≤cap) :
    ∑ i∈indices,weight i*model.rat (width i)≤C*(∑ i∈indices,weight i*width i)*logFactor d cap := by
  have h := Finset.sum_le_sum (s:=indices)
    (f:=fun i => weight i*model.rat (width i))
    (g:=fun i => weight i*(C*width i*logFactor d cap))
    (fun i hi => Nat.mul_le_mul_left _ (primitive_at_cap hg _ cap (hw i hi)))
  calc
    _≤∑ i∈indices,weight i*(C*width i*logFactor d cap) := h
    _=C*(∑ i∈indices,weight i*width i)*logFactor d cap := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem word_power (w d : ℕ) : binaryWordWidth (w^d)≤1+d*binaryWordWidth w := by
  induction d with
  | zero => simp only [pow_zero,Nat.zero_mul,Nat.add_zero]; decide
  | succ d ih =>
    have h := binaryWordWidth_mul (w^d) w
    rw [pow_succ]
    nlinarith only [h,ih]

theorem charge_word (C d w : ℕ) :
    binaryWordWidth (charge C d w)≤binaryWordWidth C+binaryWordWidth w+
      (1+d*binaryWordWidth (binaryWordWidth (w+1)+1)) := by
  have h0 := binaryWordWidth_mul C w
  have h1 := binaryWordWidth_mul (C*w) (logFactor d w)
  have h2 := word_power (binaryWordWidth (w+1)+1) d
  dsimp only [charge,logFactor] at *
  omega

theorem factor_coarse (d w : ℕ) : logFactor d w≤(w+3)^d := by
  have h := Nat.log2_le_self (w+1)
  unfold logFactor
  exact Nat.pow_le_pow_left (by dsimp only [binaryWordWidth]; omega) d

theorem charge_polynomial (C d w : ℕ) : charge C d w≤C*(w+3)^(d+1) := by
  have h := Nat.mul_le_mul (show w≤w+3 by omega) (factor_coarse d w)
  have hc := Nat.mul_le_mul_left C h
  simpa only [charge,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hc

theorem primitive_word {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) (w : ℕ) :
    binaryWordWidth (model.rat w)≤binaryWordWidth C+1+(d+1)*binaryWordWidth (w+3) := by
  have h0 := binaryWordWidth_mono ((hg w).trans (charge_polynomial C d w))
  have h1 := binaryWordWidth_mul C ((w+3)^(d+1))
  have h2 := word_power (w+3) (d+1)
  omega

end Blotto.GeneralPaperFastRationalBounds
