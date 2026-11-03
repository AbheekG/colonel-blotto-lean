import Blotto.PlayerSpecificExtendedGCDHeights

/-! The actual squarefree quotient and separation certificate have coefficient
heights bounded linearly in the original stored coefficient height. All
constants are fixed and derived from the executing dense algorithms. -/
namespace Blotto.PlayerSpecificSquarefreeHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificSquarefreeAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 6000000

def gcdHeight (H : ℕ) : ℕ := PlayerSpecificExtendedGCDHeights.height 4 (5*(H+1))
def quotientHeight (H : ℕ) : ℕ := PlayerSpecificDivisionHeights.height (gcdHeight H)
def certificateHeight (H : ℕ) : ℕ := gcdHeight (quotientHeight H)

theorem gcdHeight_ge (H : ℕ) : H≤gcdHeight H := by
  have h := PlayerSpecificExtendedGCDHeights.height_ge 4 (5*(H+1))
  unfold gcdHeight
  omega

theorem quotientHeight_ge (H : ℕ) : H≤quotientHeight H :=
  (gcdHeight_ge H).trans (PlayerSpecificDivisionHeights.height_ge _)

theorem derivative_height_four (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) :
    HasHeight (derivative p) (5*(H+1)) := by
  apply mono (derivative_height hp)
  nlinarith

theorem gcd_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) :
    HasHeight (gcdDerivative p) (gcdHeight H) ∧ (gcdDerivative p).length≤4 := by
  have h := PlayerSpecificExtendedGCDHeights.run_bounds p (derivative p) (5*(H+1))
    (mono hp (by omega)) (derivative_height_four p H hp hlen) (by omega) hlen ((derivative_length p).trans hlen)
  rw [PlayerSpecificExtendedGCD.run_gcd] at h
  exact ⟨h.1,h.2.2.2.1⟩

theorem quotient_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    HasHeight (run p) (quotientHeight H) ∧ (run p).length≤4 := by
  have hg := gcd_bounds p H hp hlen
  have h := PlayerSpecificDivisionHeights.run_height p (gcdDerivative p) (gcdHeight H)
    (mono hp (gcdHeight_ge H)) hg.1 (hH.trans (gcdHeight_ge H)) hlen hg.2
  exact ⟨h.1,(PlayerSpecificDivisionHeights.quotient_length p (gcdDerivative p)).trans hlen⟩

theorem certificate_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    HasHeight (PlayerSpecificSquarefreeCoprime.certificate p).gcd (certificateHeight H) ∧
      HasHeight (PlayerSpecificSquarefreeCoprime.certificate p).right (certificateHeight H) ∧
      (PlayerSpecificSquarefreeCoprime.certificate p).right.length≤17 := by
  have hs := quotient_bounds p H hp hH hlen
  have h := PlayerSpecificExtendedGCDHeights.run_bounds (run p) (derivative (run p)) (5*(quotientHeight H+1))
    (mono hs.1 (by omega)) (derivative_height_four (run p) _ hs.1 hs.2) (by omega) hs.2
    ((derivative_length (run p)).trans hs.2)
  exact ⟨h.1,h.2.2.1,h.2.2.2.2.2⟩

theorem headD_height (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) : RationalHeight (p.headD 0) H := by
  cases p with
  | nil => exact zero_height.mono hH
  | cons a p => exact head_height hp

theorem unitRight_bounds (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    HasHeight (PlayerSpecificSquarefreeCoprime.unitRight p) (2*certificateHeight H) ∧
      (PlayerSpecificSquarefreeCoprime.unitRight p).length≤17 := by
  have hc := certificate_bounds p H hp hH hlen
  have hs := quotientHeight_ge H
  have hg := gcdHeight_ge (quotientHeight H)
  have hC : 1≤certificateHeight H := hH.trans (hs.trans hg)
  have hh := scale_height (headD_height _ _ hc.1 hC).inv hc.2.1
  constructor
  · simpa only [PlayerSpecificSquarefreeCoprime.unitRight,two_mul] using hh
  · unfold PlayerSpecificSquarefreeCoprime.unitRight
    rw [scale_length]
    exact hc.2.2

def quotientConstant : ℕ := 193266*PlayerSpecificExtendedGCDHeights.linearConstant+9666
def certificateConstant : ℕ := 6*PlayerSpecificExtendedGCDHeights.linearConstant*(quotientConstant+1)

theorem gcd_linear (H : ℕ) : gcdHeight H≤6*PlayerSpecificExtendedGCDHeights.linearConstant*(H+1) := by
  have h := PlayerSpecificExtendedGCDHeights.fixed_degree_linear (5*(H+1))
  unfold gcdHeight
  nlinarith

theorem quotient_linear (H : ℕ) : quotientHeight H≤quotientConstant*(H+1) := by
  have h := gcd_linear H
  rw [quotientHeight,PlayerSpecificDivisionHeights.linear]
  unfold quotientConstant
  nlinarith

theorem certificate_linear (H : ℕ) : certificateHeight H≤certificateConstant*(H+1) := by
  have hg := gcd_linear (quotientHeight H)
  have hq := quotient_linear H
  have hm := Nat.mul_le_mul_left (6*PlayerSpecificExtendedGCDHeights.linearConstant) hq
  unfold certificateHeight certificateConstant
  nlinarith

theorem quotient_inputHeight (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    PlayerSpecificRationalMagnitude.inputHeight (run p)≤8*quotientHeight H+5 := by
  have hs := quotient_bounds p H hp hH hlen
  have h := inputHeight_le hs.1
  have hm := Nat.mul_le_mul_right (1+2*quotientHeight H) hs.2
  omega

theorem unitRight_inputHeight (p : Data) (H : ℕ) (hp : HasHeight p H) (hH : 1≤H) (hlen : p.length≤4) :
    PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificSquarefreeCoprime.unitRight p)≤68*certificateHeight H+18 := by
  have hs := unitRight_bounds p H hp hH hlen
  have h := inputHeight_le hs.1
  have hm := Nat.mul_le_mul_right (1+2*(2*certificateHeight H)) hs.2
  omega

end Blotto.PlayerSpecificSquarefreeHeights
