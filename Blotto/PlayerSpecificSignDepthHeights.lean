import Blotto.PlayerSpecificRefinementEndpointHeights

/-! The actual sign-refinement depth is linear in measured coefficient,
unit-certificate and original-endpoint encodings. -/
namespace Blotto.PlayerSpecificSignDepthHeights
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
open PlayerSpecificAlgebraicSignMagnitude PlayerSpecificIsolationDepthHeight
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem increment_width (n : ℕ) : binaryWordWidth (n+1)≤binaryWordWidth n+1 := by
  have hi:=binaryWordWidth_mono (Nat.succ_le_of_lt (lt_pow_binaryWordWidth n))
  rw [two_power_width] at hi
  exact hi

theorem enclosure_width (node : Interval) : binaryWordWidth (PlayerSpecificSignEnclosure.magnitude node)=
    PlayerSpecificSignEnclosure.endpointHeight node+1 := two_power_width _

theorem enlarged_width (node : Interval) : binaryWordWidth (1+PlayerSpecificSignEnclosure.magnitude node)≤
    PlayerSpecificSignEnclosure.endpointHeight node+2 := by
  have hi:=increment_width (PlayerSpecificSignEnclosure.magnitude node)
  rw [enclosure_width] at hi
  simpa only [Nat.add_comm 1] using hi

theorem gap_width (m a : Data) (node : Interval) (hlen : (PlayerSpecificAlgebraicBezout.right m a).length≤17) :
    binaryWordWidth (gapDenominator m a (PlayerSpecificSignEnclosure.magnitude node))≤
      inputHeight (PlayerSpecificAlgebraicBezout.right m a)+17*PlayerSpecificSignEnclosure.endpointHeight node+36 := by
  let M:=PlayerSpecificSignEnclosure.magnitude node
  have hs:=enlarged_width node
  have hp:=power_width (1+M) (PlayerSpecificAlgebraicBezout.right m a).length
  have hm:=Nat.mul_le_mul_left (PlayerSpecificAlgebraicBezout.right m a).length hs
  have hcap:=Nat.mul_le_mul_right (PlayerSpecificSignEnclosure.endpointHeight node+2) hlen
  have hw:=binaryWordWidth_mul (2^inputHeight (PlayerSpecificAlgebraicBezout.right m a))
    ((1+M)^(PlayerSpecificAlgebraicBezout.right m a).length)
  rw [two_power_width] at hw
  change binaryWordWidth (gapDenominator m a M)≤_ at hw
  simp only [M] at hp hw
  omega

theorem lipschitz_width (a : Data) (node : Interval) (hlen : a.length≤3) :
    binaryWordWidth (lipschitz a (PlayerSpecificSignEnclosure.magnitude node))≤
      inputHeight a+3*PlayerSpecificSignEnclosure.endpointHeight node+11 := by
  let M:=PlayerSpecificSignEnclosure.magnitude node
  have hs:=enlarged_width node
  have hp:=power_width (1+M) a.length
  have hm:=Nat.mul_le_mul_left a.length hs
  have hcap:=Nat.mul_le_mul_right (PlayerSpecificSignEnclosure.endpointHeight node+2) hlen
  have hlenw : binaryWordWidth a.length≤2 := (binaryWordWidth_mono hlen).trans_eq (by decide)
  have hfirst:=binaryWordWidth_mul a.length (2^inputHeight a)
  rw [two_power_width] at hfirst
  have hsecond:=binaryWordWidth_mul (a.length*2^inputHeight a) ((1+M)^a.length)
  have hfinal:=increment_width (a.length*2^inputHeight a*(1+M)^a.length)
  rw [Nat.add_comm (a.length*2^inputHeight a*(1+M)^a.length) 1] at hfinal
  change binaryWordWidth (lipschitz a M)≤_ at hfinal
  simp only [M] at hp hsecond hfinal
  omega

theorem depth_encoded (m a : Data) (node : Interval) (hal : a.length≤3)
    (hbl : (PlayerSpecificAlgebraicBezout.right m a).length≤17) :
    PlayerSpecificSignPrecision.depth m a node ≤ inputHeight a+inputHeight (PlayerSpecificAlgebraicBezout.right m a)+
      21*PlayerSpecificSignEnclosure.endpointHeight node+100 := by
  let M:=PlayerSpecificSignEnclosure.magnitude node
  have hM:=enclosure_width node
  have hL:=lipschitz_width a node hal
  have hB:=gap_width m a node hbl
  have hfirst:=binaryWordWidth_mul 8 M
  have hsecond:=binaryWordWidth_mul (8*M) (lipschitz a M)
  have hthird:=binaryWordWidth_mul (8*M*lipschitz a M) (gapDenominator m a M)
  rw [show binaryWordWidth 8=4 by decide] at hfirst
  change PlayerSpecificSignPrecision.depth m a node≤_ at hthird
  simp only [M] at hfirst hsecond hthird
  omega

end Blotto.PlayerSpecificSignDepthHeights
