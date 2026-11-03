import Blotto.PlayerSpecificAlgebraicInitialPrimitiveCost
import Blotto.PlayerSpecificAlgebraicActive

/-! Actual retained-root comparisons with the executed dense subtraction,
sign caller, complete copied rows and caller control. The active test
retains the native short circuit. No width or cost certificate is an input. -/
namespace Blotto.PlayerSpecificAlgebraicComparisonExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (a b difference : Data) : Trace :=
  copyRow root.polynomial++copyRow [root.interval.lo,root.interval.hi]++
    copyRow a++copyRow b++copyRow difference++[.control 1]

def run (model : RationalCostModel) (root : Candidate) (a b : Data) : Bool×ℕ :=
  let difference:=PlayerSpecificDenseExecution.subtract a b
  let signed:=PlayerSpecificPolynomialSignExecution.run model root.polynomial difference.1 root.interval
  (decide (signed.1≠.pos),price model difference.2+signed.2+price model (frame root a b difference.1))

theorem value (model : RationalCostModel) (root : Candidate) (a b : Data) :
    (run model root a b).1=PlayerSpecificAlgebraicPairStep.le model root a b := by
  simp only [run,PlayerSpecificDenseExecution.subtract_value,PlayerSpecificAlgebraicPairStep.le]

def active (model : RationalCostModel) (root : Candidate) (length value : Data) : Bool×ℕ :=
  let first:=run model root value []
  if first.1 then (false,first.2+price model [.control 1]) else
    let second:=run model root length value
    (!second.1,first.2+second.2+price model [.control 1])

theorem active_value (model : RationalCostModel) (root : Candidate) (length resource : Data) :
    (active model root length resource).1=PlayerSpecificAlgebraicActive.run model root length resource := by
  unfold active PlayerSpecificAlgebraicActive.run
  dsimp only
  split <;> rename_i h
  · simp only [value] at h
    simp only [h,Bool.not_true,Bool.false_and]
  · simp only [value] at h ⊢
    have he : PlayerSpecificAlgebraicPairStep.le model root resource []=false := Bool.eq_false_iff.mpr h
    simp only [he,Bool.not_false,Bool.true_and]

def width (H : ℕ) : ℕ := PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1)
def coefficient : ℕ := 66*PlayerSpecificPolynomialSignCost.workCoefficient+1000000

theorem price_profile (A R H : ℕ) :
    33*A*(2*H+2)*R+375333*R≤(66*A+1000000)*(H+1)*R := by
  nlinarith only [Nat.zero_le (H*R)]

theorem cost (model : RationalCostModel) (root : Candidate) (a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (ha : HasHeight a H) (hb : HasHeight b H)
    (hal : a.length≤3) (hbl : b.length≤3) (hH : 1≤H) :
    (run model root a b).2≤coefficient*(H+1)*model.rat (width H) := by
  let U:=2*H+1
  have hHU : H≤U := by dsimp [U]; omega
  have hd : HasHeight (PlayerSpecificDenseExecution.subtract a b).1 U := by
    rw [PlayerSpecificDenseExecution.subtract_value]
    simpa only [U,two_mul] using subtract_height ha hb
  have hdl : (PlayerSpecificDenseExecution.subtract a b).1.length≤3 := by
    rw [PlayerSpecificDenseExecution.subtract_value,subtract,add_length,scale_length]
    omega
  have hlarge:=PlayerSpecificAlgebraicInitialPrimitiveCost.large U
  have hW : 1≤width H := by change 1≤PlayerSpecificAlgebraicInitialPrimitiveCost.width U; omega
  have hsub:=PlayerSpecificDenseOperationCost.subtract_cost model a b H 4 ha hb hH (by omega) (by omega)
  rw [PlayerSpecificDenseOperationCost.fixed_degree_price] at hsub
  have hsub' : price model (PlayerSpecificDenseExecution.subtract a b).2≤375000*model.rat (width H) :=
    hsub.trans (Nat.mul_le_mul_left _ (model.monotone (by dsimp [width]; dsimp [U] at hlarge; omega)))
  have hsign:=PlayerSpecificAlgebraicInitialPrimitiveCost.raw_sign_cost model root.polynomial
    (PlayerSpecificDenseExecution.subtract a b).1 root.interval U hm hm0 hml (by omega)
      (mono hmH hHU) hd (mono he hHU) hv
  have hroot:=PlayerSpecificAlgebraicInitialPrimitiveCost.row_copy model root.polynomial U (mono hmH hHU) (by omega)
  have hends:=PlayerSpecificAlgebraicInitialPrimitiveCost.row_copy model [root.interval.lo,root.interval.hi] U (mono he hHU) (by simp)
  have hca:=PlayerSpecificAlgebraicInitialPrimitiveCost.row_copy model a U (mono ha hHU) (by omega)
  have hcb:=PlayerSpecificAlgebraicInitialPrimitiveCost.row_copy model b U (mono hb hHU) (by omega)
  have hcd:=PlayerSpecificAlgebraicInitialPrimitiveCost.row_copy model _ U hd (by omega)
  have hctrl : price model [.control 1]≤3*model.rat (width H) := by
    apply (price_bound model (width H) hW _ ?_).trans
    · simp only [List.length_cons,List.length_nil]; omega
    · intro e hevent
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hevent
      subst e
      change binaryWordWidth 1≤_
      have h1 : binaryWordWidth 1=1 := by decide
      rw [h1]
      exact hW
  dsimp only [run]
  simp only [frame,price_append]
  change price model (PlayerSpecificDenseExecution.subtract a b).2+
    (PlayerSpecificPolynomialSignExecution.run model root.polynomial (PlayerSpecificDenseExecution.subtract a b).1 root.interval).2+
    (price model (copyRow root.polynomial)+price model (copyRow [root.interval.lo,root.interval.hi])+
      price model (copyRow a)+price model (copyRow b)+price model (copyRow (PlayerSpecificDenseExecution.subtract a b).1)+
        price model [.control 1])≤_
  change _≤(66*PlayerSpecificPolynomialSignCost.workCoefficient+1000000)*(H+1)*model.rat (width H)
  change _≤33*PlayerSpecificPolynomialSignCost.workCoefficient*(2*H+2)*model.rat (width H) at hsign
  change _≤66*model.rat (width H) at hroot hends hca hcb hcd
  apply le_trans ?_ (price_profile PlayerSpecificPolynomialSignCost.workCoefficient (model.rat (width H)) H)
  omega

end Blotto.PlayerSpecificAlgebraicComparisonExecution
