import Blotto.PlayerSpecificRationalReconstruction

/-! Reconstruction precision and normalized denominator bound are derived
from original input encoding. Their binary size and additional bisection
depth are linear; no caller-supplied rational-root bound is required. -/
namespace Blotto.PlayerSpecificReconstructionPrecision
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude PlayerSpecificRationalRootBound
set_option autoImplicit false
set_option maxHeartbeats 5000000

def denominator (p : Data) : ℕ := 2*PlayerSpecificRootMagnitude.rootBound p*denominatorCap p
def depth (p : Data) : ℕ := PlayerSpecificRootIsolation.depth p+2*binaryWordWidth (denominator p)+4

theorem denominator_pos (p : Data) : 0<denominator p :=
  Nat.mul_pos (Nat.mul_pos (by decide) (PlayerSpecificRootMagnitude.rootBound_pos p)) (Nat.two_pow_pos _)

theorem denominator_power (p : Data) : denominator p=2^(7*inputHeight p+3) := by
  let H:=inputHeight p
  unfold denominator PlayerSpecificRootMagnitude.rootBound denominatorCap
  change 2*2^(2*H+2)*2^(5*H)=2^(7*H+3)
  calc
    _ = 2^((2*H+2)+1+5*H) := by
      rw [pow_add (2:ℕ) ((2*H+2)+1) (5*H),pow_succ (2:ℕ) (2*H+2)]
      ring
    _ = _ := by congr 1; omega

theorem denominator_width (p : Data) : binaryWordWidth (denominator p)=7*inputHeight p+4 := by
  rw [denominator_power,PlayerSpecificIsolationDepthHeight.two_power_width]

theorem depth_ge (p : Data) : PlayerSpecificRootIsolation.depth p≤depth p := by unfold depth; omega

theorem depth_linear (p : Data) (hlen : p.length≤4) :
    depth p≤(PlayerSpecificIsolationDepthHeight.linearConstant+26)*(inputHeight p+1) := by
  have hd:=PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  rw [depth,denominator_width]
  nlinarith

theorem scale_sufficient (p : Data) : 4*denominator p*denominator p≤2^depth p := by
  let D:=denominator p
  have hD : D≤2^binaryWordWidth D := (lt_pow_binaryWordWidth D).le
  have hmul:=Nat.mul_le_mul hD hD
  have hfour:=Nat.mul_le_mul_left 4 hmul
  have hp : 4*D*D≤2^(2*binaryWordWidth D+2) := by
    calc
      _ ≤ 4*(2^binaryWordWidth D*2^binaryWordWidth D) := by nlinarith only [hfour]
      _ = _ := by
        rw [show 2*binaryWordWidth D+2=binaryWordWidth D+binaryWordWidth D+2 by omega,
          pow_add (2:ℕ) (binaryWordWidth D+binaryWordWidth D) 2,pow_add (2:ℕ) (binaryWordWidth D) (binaryWordWidth D)]
        ring
  exact hp.trans (Nat.pow_le_pow_right (by decide) (by
    change 2*binaryWordWidth D+2≤PlayerSpecificRootIsolation.depth p+2*binaryWordWidth D+4
    omega))

theorem normalized_denominator (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (q : ℚ) (hq : evaluate p q=0) :
    (PlayerSpecificRootCells.normalized (PlayerSpecificRootMagnitude.rootBound p) q).den≤denominator p := by
  have h:=PlayerSpecificNormalizedRoots.denominator_bound (PlayerSpecificRootMagnitude.rootBound p)
    (PlayerSpecificRootMagnitude.rootBound_pos p) q
  have hd:=(denominator_lt p hp hlen q hq).le
  have hm:=Nat.mul_le_mul_right (2*PlayerSpecificRootMagnitude.rootBound p) hd
  exact h.trans (hm.trans_eq (by unfold denominator; ring))

end Blotto.PlayerSpecificReconstructionPrecision
