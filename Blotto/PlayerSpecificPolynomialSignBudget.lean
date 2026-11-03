import Blotto.PlayerSpecificFiniteParameterSizes

/-! The raw-polynomial sign caller derives its reduced operand and sign
input width from original encoded coefficients/endpoints. -/
namespace Blotto.PlayerSpecificPolynomialSignBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificIsolationState PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputHeight (m p : Data) (node : Interval) : ℕ := PlayerSpecificSignLinearSizes.inputHeight m p node
def remainderHeight (H : ℕ) : ℕ := 32211*H+9666
def widthCoefficient : ℕ := 300001*PlayerSpecificSignContract.widthCoefficient+2*1000000^6+10000000
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)

theorem original_heights (m p : Data) (node : Interval) :
    HasHeight m (inputHeight m p node) ∧ HasHeight p (inputHeight m p node) ∧
      HasHeight [node.lo,node.hi] (inputHeight m p node) ∧ 1 ≤ inputHeight m p node :=
  PlayerSpecificSignPreparationBudget.original_heights m p node

theorem remainder_bounds (m p : Data) (node : Interval) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hpl : p.length≤4) :
    let r:=(PlayerSpecificDivisionExecution.run p m).1.2
    Reduced m r ∧ r.length≤3 ∧ HasHeight r (remainderHeight (inputHeight m p node)) := by
  have hi:=original_heights m p node
  have hh:=PlayerSpecificDivisionExecution.heights p m _ hi.2.1 hi.1 hi.2.2.2 hpl hml
  have hr: PlayerSpecificAlgebraicReduction.Reduced m (PlayerSpecificDivisionExecution.run p m).1.2 := by
    rw [PlayerSpecificDivisionExecution.value]
    exact PlayerSpecificAlgebraicReduction.reduced m p hm hm0
  exact ⟨hr,by have hl:=hr.2; omega,hh.2⟩

theorem reduced_input_bound (m p : Data) (node : Interval) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hpl : p.length≤4) :
    PlayerSpecificSignLinearSizes.inputHeight m (PlayerSpecificDivisionExecution.run p m).1.2 node≤
      300000*(inputHeight m p node+1) := by
  have hb:=remainder_bounds m p node hm hm0 hml hpl
  have he:=inputHeight_le hb.2.2
  have hm:=Nat.mul_le_mul_right (1+2*remainderHeight (inputHeight m p node)) hb.2.1
  have hpart : PlayerSpecificRationalMagnitude.inputHeight m+PlayerSpecificSignEnclosure.endpointHeight node+1 ≤ inputHeight m p node := by
    unfold inputHeight PlayerSpecificSignLinearSizes.inputHeight
    omega
  unfold remainderHeight at he hm
  unfold PlayerSpecificSignLinearSizes.inputHeight
  nlinarith only [he,hm,hpart]

theorem copy_width (H : ℕ) :
    1+2*remainderHeight H≤width H ∧ 1+2*H≤width H ∧ 32≤width H := by
  have hm:=Nat.mul_le_mul_right (H+1) (show 10000000≤widthCoefficient by unfold widthCoefficient; omega)
  unfold width remainderHeight
  omega

theorem sign_width_profile (C S H : ℕ) (hS : S≤300000*(H+1)) : C*(S+1)≤(300001*C)*(H+1) := by
  have hh : S+1≤300001*(H+1) := by omega
  calc
    _ ≤ C*(300001*(H+1)) := Nat.mul_le_mul_left C hh
    _ = _ := by ring

theorem sign_width (S H : ℕ) (hS : S≤300000*(H+1)) : PlayerSpecificSignContract.widthCoefficient*(S+1)≤width H := by
  have hp:=sign_width_profile PlayerSpecificSignContract.widthCoefficient S H hS
  have hm:=Nat.mul_le_mul_right (H+1)
    (show 300001*PlayerSpecificSignContract.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega)
  exact hp.trans hm

theorem division_width (H : ℕ) : 2*1000000^6*(H+1)≤width H :=
  Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

end Blotto.PlayerSpecificPolynomialSignBudget
