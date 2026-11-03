import Blotto.PlayerSpecificGCDExecution

/-! Fixed-degree Euclidean source budgets derived from the checked division
and Bezout coefficient heights. Geometric growth is only in fuel <= four. -/
namespace Blotto.PlayerSpecificEuclideanBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def base : ℕ := 2*1000000^6
def step (H : ℕ) : ℕ := 32211*H+9666
def postHeight (H : ℕ) : ℕ := 1000000000*PlayerSpecificExtendedGCDHeights.linearConstant*(H+1)
def width (fuel H : ℕ) : ℕ := base*65536^(fuel+1)*(H+1)

theorem constant_pos : 1≤PlayerSpecificExtendedGCDHeights.linearConstant := by
  unfold PlayerSpecificExtendedGCDHeights.linearConstant
  omega

theorem step_ge (H : ℕ) : H≤step H := by unfold step; omega
theorem step_plus (H : ℕ) : step H+1≤65536*(H+1) := by unfold step; omega

theorem post_ge (H : ℕ) : H≤postHeight H := by
  have h := Nat.mul_le_mul_right (H+1) constant_pos
  unfold postHeight
  nlinarith

theorem tail_height (H : ℕ) : PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)≤postHeight H := by
  have h := Nat.mul_le_mul_left PlayerSpecificExtendedGCDHeights.linearConstant (step_plus H)
  unfold postHeight
  nlinarith

theorem step_le_post (H : ℕ) : step H≤postHeight H := by
  have h := Nat.mul_le_mul_right (step H+1) constant_pos
  have h' : step H+1≤PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1) := by simpa only [Nat.one_mul] using h
  exact (Nat.le_succ _).trans (h'.trans (tail_height H))

theorem product_height (H : ℕ) :
    (step H+PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)+1)*5≤postHeight H := by
  have hp := constant_pos
  have hm := Nat.mul_le_mul_right H hp
  unfold step postHeight
  nlinarith

theorem update_height (H : ℕ) : PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)+
    (step H+PlayerSpecificExtendedGCDHeights.linearConstant*(step H+1)+1)*5+1≤postHeight H := by
  have hp := constant_pos
  have hm := Nat.mul_le_mul_right H hp
  unfold step postHeight
  nlinarith

theorem coefficient_fits : 176*(1000000000*PlayerSpecificExtendedGCDHeights.linearConstant)+5000≤base := by
  norm_num [base,PlayerSpecificExtendedGCDHeights.linearConstant,PlayerSpecificExtendedGCDHeights.affine]

theorem width_lower (fuel H : ℕ) : base*(H+1)≤width fuel H := by
  have hp : 1≤65536^(fuel+1) := Nat.pow_pos (by decide)
  have hm := Nat.mul_le_mul_left base hp
  exact Nat.mul_le_mul_right (H+1) (by simpa only [Nat.mul_one] using hm)

theorem base_large : (1000000000000:ℕ)≤base := by norm_num [base]

theorem width_large (fuel H : ℕ) : 32≤width fuel H := by
  have h := width_lower fuel H
  have hc := base_large
  have hm := Nat.mul_le_mul_right (H+1) hc
  nlinarith

theorem post_width (fuel H : ℕ) : PlayerSpecificCompositeTraceFits.width (postHeight H) 21≤width fuel H := by
  have hc := Nat.mul_le_mul_right (H+1) coefficient_fits
  have hw := width_lower fuel H
  unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height postHeight
  nlinarith

theorem dense_width (fuel H : ℕ) : 40*H+64≤width fuel H := by
  have h := post_ge H
  have hw := post_width fuel H
  unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at hw
  nlinarith

theorem division_width (fuel H : ℕ) : PlayerSpecificDivisionTraceCost.width H≤width fuel H := width_lower fuel H

theorem copy_width (fuel H : ℕ) : 1+2*postHeight H≤width fuel H := by
  have hw := post_width fuel H
  unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height at hw
  nlinarith

theorem next_width (fuel H : ℕ) : width fuel (step H)≤width (fuel+1) H := by
  have hm := Nat.mul_le_mul_left (base*65536^(fuel+1)) (step_plus H)
  calc
    _ ≤ base*65536^(fuel+1)*(65536*(H+1)) := hm
    _ = width (fuel+1) H := by
      unfold width
      rw [pow_succ (65536:ℕ) (fuel+1)]
      ring

theorem width_cap (fuel H : ℕ) (hcap : fuel≤4) : width fuel H≤base*65536^5*(H+1) := by
  have h := Nat.pow_le_pow_right (by decide : 0<(65536:ℕ)) (show fuel+1≤5 by omega)
  exact Nat.mul_le_mul_right (H+1) (Nat.mul_le_mul_left base h)

end Blotto.PlayerSpecificEuclideanBudget
