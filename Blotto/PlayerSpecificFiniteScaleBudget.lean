import Blotto.PlayerSpecificFiniteScaleExecution

/-! A uniform original-cell envelope for the actual retained-scale loop.
It uses the executed defining polynomial and the proved three-step output
growth, rather than a supplied intermediate coefficient bound. -/
namespace Blotto.PlayerSpecificFiniteScaleBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 2000000

def height (H : ℕ) : ℕ := PlayerSpecificFiniteScaleHeights.height H
def widthCoefficient : ℕ := PlayerSpecificModularBudget.base*(PlayerSpecificFiniteScaleHeights.coefficient+1)+
  2*PlayerSpecificFiniteScaleHeights.coefficient+512
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)
def inputHeight (H : ℕ) : ℕ := PlayerSpecificCellCandidateHeights.height H+H+4

theorem large (H : ℕ) : PlayerSpecificCellCandidateHeights.height H≤height H ∧ H+2≤height H :=
  ⟨PlayerSpecificFiniteScaleHeights.large H,(PlayerSpecificCellCandidateHeights.large H).trans (PlayerSpecificFiniteScaleHeights.large H)⟩

theorem wide (H : ℕ) : 1+2*height H≤width H ∧ 128*(H+1)≤width H ∧ 32≤width H := by
  have hcoeff : 2*PlayerSpecificFiniteScaleHeights.coefficient+512≤widthCoefficient := by unfold widthCoefficient; omega
  have hm:=Nat.mul_le_mul_right (H+1) hcoeff
  unfold width height PlayerSpecificFiniteScaleHeights.height at *
  exact ⟨by nlinarith only [hm],by nlinarith only [hm],by nlinarith only [hm]⟩

theorem input_heights (c : Cell) (b : ℚ) (m : Data) (H : ℕ) (hc : CellHeight c H)
    (hb : RationalHeight b H) (hm : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    HasHeight m (inputHeight H) ∧ HasHeight [1/(2*b)] (inputHeight H) ∧
      HasHeight [c.state.coefficients.B2,0,c.state.coefficients.B1] (inputHeight H) := by
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hi : RationalHeight (1/(2*b)) (H+2) := by simpa only [one_div,Nat.add_comm] using (h2.mul hb).inv
  exact ⟨mono hm (by unfold inputHeight; omega),
    cons_height (hi.mono (by unfold inputHeight; omega)) (nil_height _),
    cons_height (hc.1.2.2.2.1.mono (by unfold inputHeight; omega))
      (cons_height (zero_height.mono (by unfold inputHeight; omega))
        (cons_height (hc.1.2.2.1.mono (by unfold inputHeight; omega)) (nil_height _)))⟩

theorem modular_width (H : ℕ) : PlayerSpecificModularBudget.width 3 (inputHeight H)≤width H := by
  have hh : PlayerSpecificModularHeights.height 3 (inputHeight H)≤height H :=
    PlayerSpecificFiniteScaleHeights.profile PlayerSpecificCellCandidateHeights.coefficient H
  have hhi : PlayerSpecificModularHeights.height 3 (inputHeight H)+1≤
      (PlayerSpecificFiniteScaleHeights.coefficient+1)*(H+1) := by
    unfold height PlayerSpecificFiniteScaleHeights.height at hh
    nlinarith only [hh]
  have hm:=Nat.mul_le_mul_left PlayerSpecificModularBudget.base hhi
  have hw:=Nat.mul_le_mul_right (H+1)
    (show PlayerSpecificModularBudget.base*(PlayerSpecificFiniteScaleHeights.coefficient+1)≤widthCoefficient by unfold widthCoefficient; omega)
  unfold PlayerSpecificModularBudget.width width
  exact hm.trans (by simpa only [mul_assoc] using hw)

end Blotto.PlayerSpecificFiniteScaleBudget
