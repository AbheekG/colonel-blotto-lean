import Blotto.PlayerSpecificAlgebraicExpressionNodes

/-! Shared complete backend and caller prices for the actual local
algebraic interpreter, including computed coefficient rows and indices. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionPrimitiveCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := PlayerSpecificAlgebraicComparisonExecution.coefficient+8000001000
def work (model : RationalCostModel) (S : ℕ) : ℕ := coefficient*(S+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S)

theorem initial_width (S : ℕ) : PlayerSpecificAlgebraicInitialPrimitiveCost.width S≤PlayerSpecificAlgebraicComparisonExecution.width S :=
  Nat.mul_le_mul_left PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient (show S+1≤2*S+1+1 by omega)

theorem combination_width (S : ℕ) : PlayerSpecificFieldCombinationCost.width S≤PlayerSpecificAlgebraicComparisonExecution.width S :=
  (Nat.mul_le_mul_right (S+1) (show PlayerSpecificFieldCombinationCost.widthCoefficient≤
    PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient by unfold PlayerSpecificAlgebraicInitialPrimitiveCost.widthCoefficient; omega)).trans (initial_width S)

theorem binary_cost (model : RationalCostModel) (root : Candidate) (op : Arithmetic) (a b : Data) (S : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hmS : HasHeight root.polynomial S) (haS : HasHeight a S) (hbS : HasHeight b S) (hS : 1≤S) :
    (PlayerSpecificAlgebraicExpressionExecution.binary model root op a b).2≤
      8000000000*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  have hal : a.length≤3 := by have h:=ha.2; omega
  have hbl : b.length≤3 := by have h:=hb.2; omega
  cases op with
  | add =>
    exact (PlayerSpecificFieldCombinationCost.run_cost model false root.polynomial a b hm hm0 hml S hmS haS hbS hS hal hbl).trans
      (Nat.mul_le_mul (by decide : 200000000≤8000000000) (model.monotone (combination_width S)))
  | subtract =>
    exact (PlayerSpecificFieldCombinationCost.run_cost model true root.polynomial a b hm hm0 hml S hmS haS hbS hS hal hbl).trans
      (Nat.mul_le_mul (by decide : 200000000≤8000000000) (model.monotone (combination_width S)))
  | multiply =>
    exact (PlayerSpecificAlgebraicInitialPrimitiveCost.product_cost model root.polynomial b a S hm hm0 hml ha hb hmS haS hbS).trans
      (Nat.mul_le_mul (by decide : 800000000≤8000000000) (model.monotone (initial_width S)))
  | divide =>
    exact (PlayerSpecificAlgebraicInitialPrimitiveCost.division_cost model root.polynomial a b S hm hm0 hml ha hb hmS haS hbS hS).trans
      (Nat.mul_le_mul_left _ (model.monotone (initial_width S)))

theorem constant_cost (model : RationalCostModel) (root : Candidate) (q : ℚ) (S : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmS : HasHeight root.polynomial S) (hq : RationalHeight q S) (hS : 1≤S) :
    price model (PlayerSpecificFieldCombinationContract.constant root.polynomial q).2≤
      8000000000*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) :=
  (PlayerSpecificAlgebraicInitialPrimitiveCost.constant_cost model root.polynomial q S hm hm0 hml hmS hq hS).trans
    (Nat.mul_le_mul (by decide : 200000000≤8000000000) (model.monotone (initial_width S)))

theorem frame_cost (model : RationalCostModel) (root : Candidate) (rows : List Data) (words : List ℕ) (S : ℕ)
    (hm : HasHeight root.polynomial S) (he : HasHeight [root.interval.lo,root.interval.hi] S) (hml : root.polynomial.length≤4)
    (hr : ∀ row∈rows,HasHeight row S) (hrl : ∀ row∈rows,row.length≤3)
    (hw : ∀ word∈words,word≤S) (hn : rows.length≤3) (hwn : words.length≤3) :
    price model (PlayerSpecificAlgebraicExpressionExecution.frame root rows words)≤
      500*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hh : ∀ row∈[root.polynomial,[root.interval.lo,root.interval.hi]]++rows,HasHeight row S := by
    intro row hrow
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with (hrow|hrow)|hrow
    · rw [hrow]; exact hm
    · rw [hrow]; exact he
    · exact hr row hrow
  have hl : ∀ row∈[root.polynomial,[root.interval.lo,root.interval.hi]]++rows,row.length≤21 := by
    intro row hrow
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with (hrow|hrow)|hrow
    · rw [hrow]; omega
    · rw [hrow]; simp
    · exact (hrl row hrow).trans (by decide)
  have hwords : ∀ word∈words,binaryWordWidth word≤W := fun word hword =>
    (control_width word).trans ((Nat.add_le_add_right (hw word hword) 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model ([root.polynomial,[root.interval.lo,root.interval.hi]]++rows) words S W
    hh hl hwords (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

theorem arithmetic_profile (C S R : ℕ) : 8000000000*R+500*R≤(C+8000001000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (C*(S+1)*R),Nat.zero_le (S*R),Nat.zero_le R]

theorem comparison_profile (C S R : ℕ) : C*(S+1)*R+500*R≤(C+8000001000)*(S+1)*R := by
  nlinarith only [Nat.zero_le (S*R),Nat.zero_le R]

end Blotto.PlayerSpecificAlgebraicExpressionPrimitiveCost
