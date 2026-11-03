import Blotto.PlayerSpecificSquarefreeExecution

/-! A fixed linear-width budget derived from actual quotient and certificate
heights. It is used only in proofs; executing precision uses stored data. -/
namespace Blotto.PlayerSpecificPreparationBudget
open PlayerSpecificSquarefreeHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def height (H : ℕ) : ℕ := 5*(certificateHeight H+quotientHeight H+gcdHeight H+H+1)
def width (H : ℕ) : ℕ := PlayerSpecificGCDTraceCost.capWidth (height H)

theorem input_height (H : ℕ) : H≤height H := by unfold height; omega
theorem derivative_height (H : ℕ) : 5*(H+1)≤height H := by unfold height; omega
theorem gcd_height (H : ℕ) : gcdHeight H≤height H := by unfold height; omega
theorem quotient_height (H : ℕ) : quotientHeight H≤height H := by unfold height; omega
theorem certificate_height (H : ℕ) : certificateHeight H≤height H := by unfold height; omega
theorem certificate_input (H : ℕ) : 5*(quotientHeight H+1)≤height H := by unfold height; omega
theorem unit_height (H : ℕ) : 2*certificateHeight H≤height H := by unfold height; omega

theorem cap_mono {S T : ℕ} (h : S≤T) : PlayerSpecificGCDTraceCost.capWidth S≤PlayerSpecificGCDTraceCost.capWidth T :=
  Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)

theorem cap_width (H T : ℕ) (h : T≤height H) : PlayerSpecificGCDTraceCost.capWidth T≤width H := cap_mono h

theorem width_lower (H : ℕ) : 1000000000000*(height H+1)≤width H := by
  have h := (PlayerSpecificEuclideanBudget.width_lower 0 (height H)).trans
    (PlayerSpecificEuclideanBudget.width_cap 0 (height H) (by omega))
  have hb := Nat.mul_le_mul_right (height H+1) PlayerSpecificEuclideanBudget.base_large
  exact hb.trans h

theorem width_large (H : ℕ) : 32≤width H := by have h:=width_lower H; nlinarith

theorem dense_width (H T : ℕ) (h : T≤height H) : 40*T+64≤width H := by
  have hw:=width_lower H
  nlinarith

theorem composite_width (H T N : ℕ) (h : T≤height H) (hN : N≤21) :
    PlayerSpecificCompositeTraceFits.width T N≤width H := by
  have hm := Nat.mul_le_mul (show 2*T+2≤2*height H+2 by omega) (show N+1≤22 by omega)
  have hw:=width_lower H
  unfold PlayerSpecificCompositeTraceFits.width PlayerSpecificCompositeTraceFits.height
  nlinarith

theorem division_width (H T : ℕ) (h : T≤height H) : PlayerSpecificDivisionTraceCost.width T≤width H := by
  exact (PlayerSpecificEuclideanBudget.division_width 0 T).trans
    ((PlayerSpecificEuclideanBudget.width_cap 0 T (by omega)).trans (cap_width H T h))

theorem copy_width (H T : ℕ) (h : T≤height H) : 1+2*T≤width H := by
  have hw:=dense_width H T h
  omega

def linearCoefficient : ℕ := PlayerSpecificEuclideanBudget.base*65536^5*
  (5*(certificateConstant+quotientConstant+6*PlayerSpecificExtendedGCDHeights.linearConstant+1)+1)

theorem width_linear (H : ℕ) : width H≤linearCoefficient*(H+1) := by
  have hc:=certificate_linear H
  have hq:=quotient_linear H
  have hg:=gcd_linear H
  have hh : height H+1≤(5*(certificateConstant+quotientConstant+6*PlayerSpecificExtendedGCDHeights.linearConstant+1)+1)*(H+1) := by
    unfold height
    nlinarith
  have hm:=Nat.mul_le_mul_left (PlayerSpecificEuclideanBudget.base*65536^5) hh
  unfold width PlayerSpecificGCDTraceCost.capWidth linearCoefficient
  nlinarith

end Blotto.PlayerSpecificPreparationBudget
