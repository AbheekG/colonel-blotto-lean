import Blotto.PlayerSpecificAlgebraicCoinExecution

/-! The complete actual algebraic coin has polynomial bit price, with
computed midpoint widths and no branch/sign/randomness cost oracle. -/
namespace Blotto.PlayerSpecificAlgebraicCoinCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction
set_option autoImplicit false
set_option maxHeartbeats 2500000

def polynomialCoefficient : ℕ := 2000*(192*192+192)+PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient+
  138*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+PlayerSpecificAlgebraicComparisonCost.widthCoefficient)

theorem frame_cost (model : RationalCostModel) (probability : Data) (midpoint : ℚ) (H S : ℕ)
    (hp : HasHeight probability S) (hm : RationalHeight midpoint S) (hpl : probability.length≤3) (hHS : H≤S) :
    price model (PlayerSpecificAlgebraicCoinExecution.frame probability midpoint H)≤
      138*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model [probability,[midpoint]] [H,1] S W
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with hrow|hrow
        · rw [hrow]; exact hp
        · rw [hrow]; exact cons_height hm (nil_height _))
    (by intro row hrow; simp only [List.mem_cons,List.not_mem_nil,or_false] at hrow; rcases hrow with hrow|hrow
        · rw [hrow]; omega
        · rw [hrow]; simp)
    (by intro word hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw; rcases hw with hw|hw
        · rw [hw]; exact (control_width H).trans ((Nat.add_le_add_right hHS 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
        · rw [hw]; exact (control_width 1).trans (by have h:32≤W:=(PlayerSpecificAlgebraicActiveListCost.width_large S).1; omega))
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  simpa only [PlayerSpecificAlgebraicCoinExecution.frame,List.length_cons,List.length_nil] using hc

theorem cost (root : Candidate) (probability : Data) (T H : ℕ) (bits : Fin H → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hp : HasHeight probability T) (hpr : Reduced root.polynomial probability) :
    (PlayerSpecificAlgebraicCoinExecution.run RationalCostModel.schoolbook root probability H bits).2≤
      polynomialCoefficient*(T+H+3)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=T+H+2
  let midpoint:=(PlayerSpecificMidpointExecution.run model H bits).1
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hTS : T≤S := by dsimp [S]; omega
  have hHS : H+2≤S := by dsimp [S]; omega
  have hS : 1≤S := by dsimp [S]; omega
  have hmid : RationalHeight midpoint S := by
    change RationalHeight (PlayerSpecificMidpointExecution.run model H bits).1 S
    rw [PlayerSpecificMidpointExecution.value]
    exact (dyadicMidpointSample_height H bits).mono hHS
  have hpl : probability.length≤3 := by have hl:=hpr.2; omega
  have hmidrow : HasHeight [midpoint] S := cons_height hmid (nil_height _)
  have hc:=PlayerSpecificAlgebraicComparisonCost.comparison root probability [midpoint] S hm hm0 hml (mono hmH hTS) (mono he hTS) hv
    (mono hp hTS) hmidrow hpl (by simp) hS
  have hmCost:=PlayerSpecificMidpointCost.polynomial_cost H bits
  have hpow : (H+1)^3≤(S+1)^3 := Nat.pow_le_pow_left (by dsimp [S]; omega) 3
  have hmCost':=(hmCost.trans (Nat.mul_le_mul_left _ hpow))
  have hf:=frame_cost model probability midpoint H S (mono hp hTS) hmid hpl (by omega)
  rw [PlayerSpecificAlgebraicComparisonCost.width_linear] at hf
  have hquadratic:=PlayerSpecificAlgebraicInverseContract.quadratic_profile 138 PlayerSpecificAlgebraicComparisonCost.widthCoefficient (S+1) (by omega)
  have hpowers : (S+1)^2≤(S+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have hf' : price model (PlayerSpecificAlgebraicCoinExecution.frame probability midpoint H)≤
      (138*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+PlayerSpecificAlgebraicComparisonCost.widthCoefficient))*(S+1)^3 := by
    apply (hf.trans hquadratic).trans
    exact Nat.mul_le_mul_left _ hpowers
  change (PlayerSpecificMidpointExecution.run model H bits).2+
    (PlayerSpecificAlgebraicComparisonExecution.run model root probability [midpoint]).2+
      price model (PlayerSpecificAlgebraicCoinExecution.frame probability midpoint H)≤_
  have hsum:=Nat.add_le_add (Nat.add_le_add hmCost' hc) hf'
  apply hsum.trans_eq
  change _=(2000*(192*192+192)+PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient+
    138*(PlayerSpecificAlgebraicComparisonCost.widthCoefficient^2+PlayerSpecificAlgebraicComparisonCost.widthCoefficient))*(S+1)^3
  ring

end Blotto.PlayerSpecificAlgebraicCoinCost
