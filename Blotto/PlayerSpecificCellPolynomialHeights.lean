import Blotto.PlayerSpecificRecognitionInputHeights

/-! Actual cubic and exact candidate-test polynomials have linear sizes
in the checked rational cell encoding. -/
namespace Blotto.PlayerSpecificCellPolynomialHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCellTests
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem cubic_height (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H) :
    HasHeight (cubic c.state.coefficients b) (2*H) := by
  have ha : RationalHeight (-b*c.state.coefficients.A2) (2*H) := by
    simpa only [two_mul,neg_mul] using (hb.mul hc.1.2.1).neg
  have hb' : RationalHeight (-b*c.state.coefficients.A1) (2*H) := by
    simpa only [two_mul,neg_mul] using (hb.mul hc.1.1).neg
  exact cons_height ha (cons_height (hc.1.2.2.2.1.mono (by omega))
    (cons_height hb' (cons_height (hc.1.2.2.1.mono (by omega)) (nil_height _))))

theorem cubic_encoding (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H) :
    PlayerSpecificRationalMagnitude.inputHeight (cubic c.state.coefficients b)≤16*H+5 := by
  have h:=inputHeight_le (cubic_height c b H hc hb)
  change PlayerSpecificRationalMagnitude.inputHeight (cubic c.state.coefficients b)≤4*(1+2*(2*H))+1 at h
  omega

theorem tests (c : Cell) (H : ℕ) (hc : CellHeight c H) (hH : 1≤H) :
    HasHeight positive (4*H+4) ∧ HasHeight (lower c) (4*H+4) ∧
      (∀ q∈c.upper,HasHeight (upper q) (4*H+4)) ∧
      HasHeight (firstGate c) (4*H+4) ∧ HasHeight (secondGate c) (4*H+4) := by
  have h0 : RationalHeight (0:ℚ) (4*H+4) := zero_height.mono (by omega)
  have h1 : RationalHeight (1:ℚ) (4*H+4) := one_height.mono (by omega)
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hfirst:=hc.1.2.2.2.1.sub (h2.mul hc.1.2.2.2.2)
  have hsecond:=h2.neg.mul hc.2.2.2
  refine ⟨cons_height h0 (cons_height h1 (nil_height _)),
    cons_height (hc.2.1.neg.mono (by omega)) (cons_height h1 (nil_height _)),?_,?_,?_⟩
  · intro q hq
    exact cons_height ((hc.2.2.1 q hq).mono (by omega)) (cons_height h1.neg (nil_height _))
  · exact cons_height (hfirst.mono (by omega)) (cons_height h0 (cons_height (hc.1.2.2.1.mono (by omega)) (nil_height _)))
  · exact cons_height (hc.1.2.2.2.1.mono (by omega))
      (cons_height (by simpa only [neg_mul] using hsecond.mono (by omega : 2+H≤4*H+4))
        (cons_height (hc.1.2.2.1.mono (by omega)) (nil_height _)))

end Blotto.PlayerSpecificCellPolynomialHeights
