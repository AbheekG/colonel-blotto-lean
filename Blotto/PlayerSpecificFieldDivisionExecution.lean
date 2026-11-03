import Blotto.PlayerSpecificFieldUnaryContract

/-! Actual division caches one exact inverse and feeds its reduced return
directly into modular multiplication, retaining every input/output copy. -/
namespace Blotto.PlayerSpecificFieldDivisionExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def coefficientHeight (H : ℕ) : ℕ := PlayerSpecificAlgebraicInverseExecution.height H+H+1
def height (H : ℕ) : ℕ := PlayerSpecificModularHeights.height 3 (coefficientHeight H)
def width (H : ℕ) : ℕ := PlayerSpecificAlgebraicInverseExecution.width H+
  PlayerSpecificModularBudget.width 3 (coefficientHeight H)+1024*(height H+H+1)+1024
def frame (m a b result : Data) : Trace := copyRow m++copyRow a++copyRow b++copyRow result++[.control 1]
def run (model : RationalCostModel) (m a b : Data) : Data×ℕ :=
  let inverse:=PlayerSpecificAlgebraicInverseExecution.run model m b
  let product:=PlayerSpecificModularExecution.run model m inverse.1 a
  (product.1,inverse.2+product.2+price model (frame m a b product.1))

theorem value (model : RationalCostModel) (m a b : Data) : (run model m a b).1=PlayerSpecificAlgebraicField.divide m a b := by
  simp only [run,PlayerSpecificModularExecution.value,PlayerSpecificAlgebraicInverseExecution.value,
    PlayerSpecificAlgebraicField.divide,PlayerSpecificAlgebraicField.times]

theorem bounds (model : RationalCostModel) (m a b : Data) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b) (H : ℕ)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    Reduced m (run model m a b).1 ∧ (run model m a b).1.length≤3 ∧ HasHeight (run model m a b).1 (height H) := by
  have hi:=PlayerSpecificAlgebraicInverseExecution.bounds model m b hm hm0 hml hb H hmH hbH hH
  have hU : H≤coefficientHeight H := by unfold coefficientHeight; omega
  have hI : PlayerSpecificAlgebraicInverseExecution.height H≤coefficientHeight H := by unfold coefficientHeight; omega
  have hcoef := mono hi.1 hI
  have hmcoef:=mono hmH hU
  have hacoef:=mono haH hU
  have hal : a.length≤3 := by have hl:=ha.2; omega
  have hh:=PlayerSpecificModularHeights.run_height m (PlayerSpecificAlgebraicInverseExecution.run model m b).1 a
    hm hm0 hml hi.2 (coefficientHeight H) hmcoef hcoef hacoef
  have hmheight:=PlayerSpecificModularHeights.fuel_mono (coefficientHeight H) hal
  have hr:=PlayerSpecificModularHorner.reduced m (PlayerSpecificAlgebraicInverseExecution.run model m b).1 a hm hm0
  simp only [run,PlayerSpecificModularExecution.value]
  exact ⟨hr,by have hl:=hr.2; omega,mono hh hmheight⟩

end Blotto.PlayerSpecificFieldDivisionExecution
