import Blotto.PlayerSpecificSquarefreeHeights

/-! The actual computed cubic-isolation depth is linear in the original
rational input encoding. This discharges the precision/fuel size bound;
the rational-primitive cost trace is handled separately. -/
namespace Blotto.PlayerSpecificIsolationDepthHeight
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude PlayerSpecificPolynomialHeights
open PlayerSpecificRootMagnitude PlayerSpecificRootSeparation PlayerSpecificSquarefreeCoprime
open PlayerSpecificSquarefreeHeights
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem power_width (n k : ℕ) : binaryWordWidth (n^k)≤k*binaryWordWidth n+1 := by
  induction k with
  | zero => simp only [pow_zero,binaryWordWidth,show Nat.log2 1=0 by decide,Nat.zero_mul,Nat.zero_add,Nat.le_refl]
  | succ k ih =>
    rw [pow_succ]
    have h := binaryWordWidth_mul (n^k) n
    rw [Nat.add_mul]
    omega

theorem root_width (p : Data) : binaryWordWidth (rootBound p)=2*inputHeight p+3 := by
  simp only [rootBound,binaryWordWidth,Nat.log2_two_pow]

theorem two_power_width (s : ℕ) : binaryWordWidth (2^s)=s+1 := by
  simp only [binaryWordWidth,Nat.log2_two_pow]

theorem small_add_width (p : Data) :
    binaryWordWidth (1+rootBound p)≤2*inputHeight p+4 ∧
      binaryWordWidth (1+3*rootBound p)≤2*inputHeight p+5 := by
  have hm : 1≤rootBound p := rootBound_pos p
  have h1 : 1+rootBound p≤2^(2*inputHeight p+3) := by
    rw [show 2*inputHeight p+3=(2*inputHeight p+2)+1 by omega,pow_add]
    change 1+rootBound p≤rootBound p*2^1
    omega
  have h3 : 1+3*rootBound p≤2^(2*inputHeight p+4) := by
    rw [show 2*inputHeight p+4=(2*inputHeight p+2)+2 by omega,pow_add]
    change 1+3*rootBound p≤rootBound p*2^2
    norm_num only [Nat.reducePow]
    omega
  have hb1 := binaryWordWidth_mono h1
  have hb3 := binaryWordWidth_mono h3
  simp only [binaryWordWidth,Nat.log2_two_pow] at hb1 hb3
  exact ⟨hb1,hb3⟩

theorem depth_encoded (p : Data) (hlen : (unitRight p).length≤17) :
    PlayerSpecificRootIsolation.depth p ≤ inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)+
      inputHeight (unitRight p)+40*inputHeight p+100 := by
  have hsmall := small_add_width p
  have hp := power_width (1+rootBound p) (unitRight p).length
  have hmul := Nat.mul_le_mul_left (unitRight p).length hsmall.1
  have hcap := Nat.mul_le_mul_right (2*inputHeight p+4) hlen
  have hb := binaryWordWidth_mul (2^inputHeight (unitRight p)) ((1+rootBound p)^(unitRight p).length)
  rw [two_power_width] at hb
  change binaryWordWidth (bezoutBound p)≤_ at hb
  have hd := binaryWordWidth_mul (2^inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)) (1+3*rootBound p)
  rw [two_power_width] at hd
  change binaryWordWidth (derivativeBound p)≤_ at hd
  have hsep := binaryWordWidth_mul (derivativeBound p) (bezoutBound p)
  change binaryWordWidth (separationDenominator p)≤_ at hsep
  have hi := binaryWordWidth_mul 2 (rootBound p)
  have ho := binaryWordWidth_mul (2*rootBound p) (separationDenominator p)
  change PlayerSpecificRootIsolation.depth p≤_ at ho
  rw [root_width,show binaryWordWidth 2=2 by decide] at hi
  omega

def linearConstant : ℕ := 8*quotientConstant+68*certificateConstant+200

theorem depth_linear (p : Data) (hlen : p.length≤4) :
    PlayerSpecificRootIsolation.depth p≤linearConstant*(inputHeight p+1) := by
  have hH : 1 ≤ inputHeight p := by unfold inputHeight; omega
  have hp := input_height p
  have hl := (unitRight_bounds p _ hp hH hlen).2
  have hd := depth_encoded p hl
  have hs := quotient_inputHeight p _ hp hH hlen
  have hb := unitRight_inputHeight p _ hp hH hlen
  have hsq := quotient_linear (inputHeight p)
  have hcert := certificate_linear (inputHeight p)
  unfold linearConstant
  nlinarith

theorem traversal_linear (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    PlayerSpecificIsolationForest.visits (PlayerSpecificIsolationState.prepare p) (PlayerSpecificRootIsolation.depth p)
      (PlayerSpecificRootMagnitude.initial p (PlayerSpecificIsolationState.prepare p))≤
        (6*linearConstant+1)*(inputHeight p+1) := by
  have hv := PlayerSpecificRootIsolation.visit_bound p hp hlen
  have hd := depth_linear p hlen
  nlinarith

end Blotto.PlayerSpecificIsolationDepthHeight
