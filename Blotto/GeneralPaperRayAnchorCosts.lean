import Blotto.GeneralPaperRayHighSound

/-! Rational anchor readers for the actual ray. Zero labels remain fixed;
positive labels read the corresponding variable. The fixed-point DP costs
therefore are exactly the original whole-tuple affine sums.
-/
namespace Blotto.GeneralPaperRayAnchorCosts
open RationalOrderCell GeneralPaperRayAffine
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2500000

def anchorQ {m K : ℕ} (x : Variable m K → ℚ) (j : Fin m) (l : Fin K) : ℚ :=
  if hz : l.val=0 then 0 else x (j,⟨l.val-1,by have hl := l.isLt; omega⟩)

def costs {m K : ℕ} (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) (l : Fin K) : ℚ :=
  anchorQ x j l+t*anchorQ w j l

theorem anchor_cast {m K : ℕ} (x : Variable m K → ℚ) (j : Fin m) (l : Fin K) :
    (anchorQ x j l:ℝ)=refValue (fun v => (x v:ℝ)) (tupleReference j l) := by
  have hk : l.val≠K := Nat.ne_of_lt l.isLt
  by_cases hz : l.val=0 <;> simp only [anchorQ,tupleReference,reference,hz,dite_true,dite_false,hk,refValue,Rat.cast_zero]

theorem costs_cast {m K : ℕ} (x w : Variable m K → ℚ) (t : ℚ) (j : Fin m) (l : Fin K) :
    (costs x w t j l:ℝ)=refValue (fun v => (x v:ℝ)+(t:ℝ)*(w v:ℝ)) (tupleReference j l) := by
  have hk : l.val≠K := Nat.ne_of_lt l.isLt
  by_cases hz : l.val=0 <;>
    simp only [costs,anchorQ,tupleReference,reference,hz,dite_true,dite_false,hk,refValue,
      Rat.cast_zero,mul_zero,add_zero,Rat.cast_add,Rat.cast_mul]

theorem tuple_cast {m K : ℕ} (x w : Variable m K → ℚ) (t : ℚ) (labels : Fin m → Fin K) :
    ((∑ j,costs x w t j (labels j):ℚ):ℝ)=tupleSum (fun v => (x v:ℝ)+(t:ℝ)*(w v:ℝ)) labels := by
  simp only [Rat.cast_sum,tupleSum,costs_cast]

theorem tuple_affine {m K : ℕ} (x w : Variable m K → ℚ) (t : ℚ) (labels : Fin m → Fin K) :
    (∑ j,costs x w t j (labels j))=(∑ j,anchorQ x j (labels j))+t*(∑ j,anchorQ w j (labels j)) := by
  simp only [costs,Finset.sum_add_distrib,Finset.mul_sum]

theorem costs_zero {m K : ℕ} (x w : Variable m K → ℚ) : costs x w 0=anchorQ x := by
  funext j l
  simp only [costs,zero_mul,add_zero]

end Blotto.GeneralPaperRayAnchorCosts
