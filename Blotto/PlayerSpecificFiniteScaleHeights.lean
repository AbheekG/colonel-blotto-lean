import Blotto.PlayerSpecificCellCandidateHeights

/-! Linear-in-cell heights of the actually retained algebraic scale.
Its modular Horner loop has exactly three coefficient positions. -/
namespace Blotto.PlayerSpecificFiniteScaleHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalCells PlayerSpecificRationalCellHeights
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 1000000^3*(PlayerSpecificCellCandidateHeights.coefficient+6)
def height (H : ℕ) : ℕ := coefficient*(H+1)

theorem profile (C H : ℕ) : 1000000^3*((C*(H+1)+H+4)+1)≤(1000000^3*(C+6))*(H+1) := by
  have hs : C*(H+1)+H+4+1≤(C+6)*(H+1) := by nlinarith
  have hm:=Nat.mul_le_mul_left (1000000^3) hs
  simpa only [mul_assoc] using hm

theorem scale_height (c : Cell) (b : ℚ) (m : Data) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4)
    (hmH : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    HasHeight (PlayerSpecificFiniteParameterReturn.scale c b m) (height H) := by
  let G:=PlayerSpecificCellCandidateHeights.height H+H+4
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hi : RationalHeight (1/(2*b)) (H+2) := by
    simpa only [one_div,Nat.add_comm] using (h2.mul hb).inv
  have hmG : HasHeight m G := mono hmH (by dsimp only [G]; omega)
  have hbG : HasHeight [1/(2*b)] G := cons_height (hi.mono (by dsimp only [G]; omega)) (nil_height G)
  have haG : HasHeight [c.state.coefficients.B2,0,c.state.coefficients.B1] G :=
    cons_height (hc.1.2.2.2.1.mono (by dsimp only [G]; omega))
      (cons_height (zero_height.mono (by dsimp only [G]; omega))
        (cons_height (hc.1.2.2.1.mono (by dsimp only [G]; omega)) (nil_height G)))
  have hr:=PlayerSpecificModularHeights.run_height m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]
    hm hm0 hml (by simp) G hmG hbG haG
  have hp:=profile PlayerSpecificCellCandidateHeights.coefficient H
  apply mono hr
  exact hp

theorem large (H : ℕ) : PlayerSpecificCellCandidateHeights.height H≤height H := by
  have hh : PlayerSpecificCellCandidateHeights.coefficient≤coefficient := by unfold coefficient; omega
  exact Nat.mul_le_mul_right _ hh

end Blotto.PlayerSpecificFiniteScaleHeights
