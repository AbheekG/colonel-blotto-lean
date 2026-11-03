import Blotto.PlayerSpecificReconstructionCache

/-! Derived envelopes for all actually constructed reconstruction controls
and source-word fields. They also bound arbitrary natural arithmetic calls
with the proved literal operand/result range, without an aggregate oracle. -/
namespace Blotto.PlayerSpecificReconstructionCacheBudget
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude PlayerSpecificIntegerBudget
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem coefficient_large : PlayerSpecificIsolationDepthHeight.linearConstant+100≤coefficient := by
  unfold coefficient
  omega

theorem parameter_bound (p : Data) (hlen : p.length≤4) :
    8*inputHeight p+(PlayerSpecificReconstructionPrecision.depth p+3)+5≤height (inputHeight p) := by
  have hd:=PlayerSpecificReconstructionPrecision.depth_linear p hlen
  have hm:=Nat.mul_le_mul_right (inputHeight p+1) coefficient_large
  unfold height
  nlinarith

theorem controls (p : Data) (hlen : p.length≤4) :
    inputHeight p≤height (inputHeight p) ∧
      7*inputHeight p+4≤height (inputHeight p) ∧
      14*inputHeight p+12≤height (inputHeight p) ∧
      PlayerSpecificRootIsolation.depth p≤height (inputHeight p) ∧
      PlayerSpecificReconstructionPrecision.depth p+3≤height (inputHeight p) := by
  have hp:=parameter_bound p hlen
  have hm:=Nat.mul_le_mul_right (inputHeight p+1) coefficient_ge
  have hd:=PlayerSpecificReconstructionPrecision.depth_ge p
  unfold height at *
  omega

theorem small_word (H n : ℕ) (hn : n≤16384*(height H+1)) : 1+binaryWordWidth n≤width H := by
  have htop:=binaryWordWidth_mul 16384 (height H+1)
  have hc : binaryWordWidth 16384=15 := by decide
  have hs:=PlayerSpecificRationalTrace.control_width (height H+1)
  have hm:=binaryWordWidth_mono hn
  unfold width
  omega

theorem binary_cost (model : RationalCostModel) (H : ℕ) (op : ℕ → ℕ → ℕ) (a b : ℕ)
    (ha : a≤16384*(height H+1)) (hb : b≤16384*(height H+1)) (hc : op a b≤16384*(height H+1)) :
    (PlayerSpecificNaturalExecution.binary model op a b).2≤64*model.rat (width H) :=
  PlayerSpecificNaturalExecution.binary_cost model op a b (width H)
    (small_word H a ha) (small_word H b hb) (small_word H (op a b) hc)

theorem dyadic_cost (model : RationalCostModel) (H exponent : ℕ) (he : exponent≤height H) :
    (PlayerSpecificNaturalExecution.power model 2 exponent).2≤256*(height H+1)*model.rat (width H) := by
  have hp:=PlayerSpecificNaturalExecution.power_cost model 2 exponent
  have ht : binaryWordWidth 2=2 := by decide
  have hw : PlayerSpecificNaturalExecution.powerWidth 2 exponent≤width H := by
    unfold PlayerSpecificNaturalExecution.powerWidth width
    rw [ht]
    omega
  exact (hp.trans (Nat.mul_le_mul_left (256*(exponent+1)) (model.monotone hw))).trans
    (Nat.mul_le_mul_right (model.rat (width H)) (Nat.mul_le_mul_left 256 (Nat.add_le_add_right he 1)))

theorem source_word (model : RationalCostModel) (p : Data) (hlen : p.length≤4) :
    (PlayerSpecificReconstructionCache.run model p).1.word≤width (inputHeight p) := by
  have h:=parameter_bound p hlen
  rw [PlayerSpecificReconstructionCache.word_value,PlayerSpecificReconstructionPrecision.denominator_width]
  unfold width
  nlinarith

theorem query_width (model : RationalCostModel) (p : Data) :
    GeneralPaperCFOperandPrice.width (PlayerSpecificReconstructionCache.run model p).1.lambda
      (PlayerSpecificReconstructionCache.run model p).1.denominator≤(PlayerSpecificReconstructionCache.run model p).1.word := by
  rw [PlayerSpecificReconstructionCache.lambda_value,PlayerSpecificReconstructionCache.denominator_value,
    PlayerSpecificReconstructionCache.word_value]
  unfold GeneralPaperCFOperandPrice.width
  omega

end Blotto.PlayerSpecificReconstructionCacheBudget
