import Blotto.PlayerSpecificRationalPrecisionExecution

/-! All operands of the actual scaled dyadic precision choice have
uniform word lengths derived from C and the supplied rational epsilon. -/
namespace Blotto.PlayerSpecificRationalPrecisionSourceSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputWidth (C : ℕ) (epsilon : ℚ) : ℕ :=
  binaryWordWidth C+rationalWordWidth epsilon+16
def width (C : ℕ) (epsilon : ℚ) : ℕ := 4*inputWidth C epsilon+40

theorem numerator_width (C : ℕ) (epsilon : ℚ) :
    binaryWordWidth (C*epsilon.den) ≤ inputWidth C epsilon := by
  have h:=binaryWordWidth_mul C epsilon.den
  dsimp only [inputWidth,rationalWordWidth]
  omega

theorem denominator_width (C : ℕ) (epsilon : ℚ) :
    binaryWordWidth epsilon.num.toNat ≤ inputWidth C epsilon := by
  have hn : epsilon.num.toNat≤epsilon.num.natAbs := by omega
  have hw:=binaryWordWidth_mono hn
  dsimp only [inputWidth,rationalWordWidth]
  omega

theorem candidate_bound (C : ℕ) (epsilon : ℚ) :
    binaryWordWidth (C*epsilon.den)-binaryWordWidth epsilon.num.toNat ≤
      inputWidth C epsilon := by
  have hn:=numerator_width C epsilon
  omega

theorem power_width (C : ℕ) (epsilon : ℚ) :
    binaryWordWidth (2^(binaryWordWidth (C*epsilon.den)-
      binaryWordWidth epsilon.num.toNat)) ≤ inputWidth C epsilon+1 := by
  rw [PlayerSpecificIsolationDepthHeight.two_power_width]
  have h:=candidate_bound C epsilon
  omega

theorem scaled_width (C : ℕ) (epsilon : ℚ) :
    binaryWordWidth (epsilon.num.toNat *
      2^(binaryWordWidth (C*epsilon.den)-binaryWordWidth epsilon.num.toNat))≤
      2*inputWidth C epsilon+1 := by
  have h:=binaryWordWidth_mul epsilon.num.toNat
    (2^(binaryWordWidth (C*epsilon.den)-binaryWordWidth epsilon.num.toNat))
  have ha:=denominator_width C epsilon
  have hb:=power_width C epsilon
  omega

theorem precision_bound (C : ℕ) (epsilon : ℚ) (hC : 0<C) (he : 0<epsilon) :
    PlayerSpecificRationalPrecision.exponent C epsilon ≤ inputWidth C epsilon+1 := by
  have ha : 0<C*epsilon.den := Nat.mul_pos hC epsilon.den_pos
  have hb : 0<epsilon.num.toNat :=
    Int.pos_iff_toNat_pos.mp (Rat.num_pos.mpr he)
  unfold PlayerSpecificRationalPrecision.exponent
  rw [←widthRatioPrecision_eq (C*epsilon.den) epsilon.num.toNat ha hb]
  simp only [widthRatioPrecision,widthRatioCandidate]
  by_cases ht : C*epsilon.den≤epsilon.num.toNat <<<
      (binaryWordWidth (C*epsilon.den)-binaryWordWidth epsilon.num.toNat)
  · simp only [ht,ite_true]
    have hc:=candidate_bound C epsilon
    omega
  · simp only [ht,ite_false]
    have hc:=candidate_bound C epsilon
    omega

end Blotto.PlayerSpecificRationalPrecisionSourceSizes
