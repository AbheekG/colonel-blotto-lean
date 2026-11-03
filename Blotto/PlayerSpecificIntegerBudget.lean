import Blotto.PlayerSpecificIntegerPreparation

/-! Original-encoding linear envelopes for every actual integer preparation
operand. These are proof constants, not executing precision parameters. -/
namespace Blotto.PlayerSpecificIntegerBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
open PlayerSpecificSquarefreeHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

def coefficient : ℕ := 1024*(certificateConstant+quotientConstant+
  PlayerSpecificIsolationDepthHeight.linearConstant+PlayerSpecificPreparationBudget.linearCoefficient+1)
def height (H : ℕ) : ℕ := coefficient*(H+1)
def width (H : ℕ) : ℕ := 4096*(height H+1)

theorem coefficient_ge : 1024≤coefficient := by unfold coefficient; omega
theorem input_le (H : ℕ) : H≤height H := by
  have hm:=Nat.mul_le_mul_right (H+1) coefficient_ge
  unfold height
  nlinarith
theorem quotient_le (H : ℕ) : quotientConstant*(H+1)≤height H := by
  apply Nat.mul_le_mul_right
  unfold coefficient
  omega
theorem unit_le (H : ℕ) : 2*certificateConstant*(H+1)≤height H := by
  apply Nat.mul_le_mul_right
  unfold coefficient
  omega
theorem certificate_le (H : ℕ) : certificateConstant*(H+1)≤height H := by have h:=unit_le H; nlinarith
theorem depth_le (H : ℕ) : PlayerSpecificIsolationDepthHeight.linearConstant*(H+1)≤height H := by
  apply Nat.mul_le_mul_right
  unfold coefficient
  omega
theorem polynomial_width (H : ℕ) : PlayerSpecificPreparationBudget.width H≤width H := by
  have hc : PlayerSpecificPreparationBudget.linearCoefficient≤coefficient := by unfold coefficient; omega
  have hm:=Nat.mul_le_mul_right (H+1) hc
  have h:=PlayerSpecificPreparationBudget.width_linear H
  unfold width height
  nlinarith
theorem measurement_width (H T : ℕ) (h : T≤height H) : PlayerSpecificInputWidthExecution.width T≤width H := by
  unfold PlayerSpecificInputWidthExecution.width width
  omega
theorem enclosure_width (H : ℕ) : PlayerSpecificEnclosureExecution.width H≤width H := by
  have h:=input_le H
  unfold PlayerSpecificEnclosureExecution.width width
  omega
theorem width_large (H : ℕ) : 32≤width H := by unfold width; omega
theorem copy_width (H T : ℕ) (h : T≤height H) : 1+2*T≤width H := by unfold width; omega

theorem separation_size (p : Data) (hlen : p.length≤4) :
    PlayerSpecificSeparationExecution.size (PlayerSpecificRootMagnitude.rootBound p)
      (inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)) (inputHeight (PlayerSpecificSquarefreeCoprime.unitRight p))≤height (inputHeight p) := by
  let H:=inputHeight p
  have hp:=input_height p
  have hH : 1≤H := by unfold H inputHeight; omega
  have hq:=quotient_inputHeight p H hp hH hlen
  have hb:=unitRight_inputHeight p H hp hH hlen
  have hql:=quotient_linear H
  have hbl:=certificate_linear H
  have hr:=PlayerSpecificIsolationDepthHeight.root_width p
  have hcoef : 8*quotientConstant+68*certificateConstant+60≤coefficient := by unfold coefficient; omega
  have hm:=Nat.mul_le_mul_right (H+1) hcoef
  unfold PlayerSpecificSeparationExecution.size height
  nlinarith

theorem separation_width (p : Data) (hlen : p.length≤4) :
    PlayerSpecificSeparationExecution.width (PlayerSpecificRootMagnitude.rootBound p)
      (inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)) (inputHeight (PlayerSpecificSquarefreeCoprime.unitRight p))≤width (inputHeight p) := by
  have h:=separation_size p hlen
  unfold PlayerSpecificSeparationExecution.width width
  omega

theorem separation_word (p : Data) (hlen : p.length≤4) :
    binaryWordWidth (PlayerSpecificRootSeparation.separationDenominator p)≤20*height (inputHeight p) := by
  have hH : 1 ≤ inputHeight p := by unfold inputHeight; omega
  have hlenB := (unitRight_bounds p _ (input_height p) hH hlen).2
  have h:= (PlayerSpecificSeparationExecution.words (PlayerSpecificRootMagnitude.rootBound p)
    (inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)) (inputHeight (PlayerSpecificSquarefreeCoprime.unitRight p))
    (PlayerSpecificSquarefreeCoprime.unitRight p).length hlenB).2.2
  change binaryWordWidth (PlayerSpecificRootSeparation.separationDenominator p)≤_ at h
  exact h.trans (Nat.mul_le_mul_left 20 (separation_size p hlen))

end Blotto.PlayerSpecificIntegerBudget
