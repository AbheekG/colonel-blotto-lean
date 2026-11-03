import Blotto.GeneralPaperBasisStageSize

/-! Raw native Schur/adjugate-update operands, before exact division.
Bounds are polynomial in the dimension, original-row coefficient bound
and cache envelope. The already proved exact-division identity permits a
quotient bound without assuming cancellation in its numerator.
-/
namespace Blotto.GeneralPaperBasisUpdateOperandSize
open GeneralPaperBasisStoredProducts
set_option autoImplicit false
set_option maxHeartbeats 4500000

def nextBound (n H B : ℕ) : ℕ := B*H+n*B*(n*H*B)

theorem determinant {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) (H B : ℕ)
    (hD : D.natAbs≤H) (hA : ∀ i j,((A.read i).read j).natAbs≤H)
    (hu : ∀ i,(u.read i).natAbs≤B) (hv : ∀ i,(v.read i).natAbs≤B) (ha : a.natAbs≤B) :
    (GeneralPaperBasisStoredStep.run D A u v a).determinant.natAbs≤nextBound n H B := by
  have hAU := GeneralPaperStoredProductSize.mulVec A u H B hA hu
  have hDot := GeneralPaperIntegerDotSize.run_bound v.read (mulVecRun A u).1.read B (n*H*B) hv hAU
  have hProduct : (a*D).natAbs≤B*H := by rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hD
  have hh := Int.natAbs_add_le (a*D) (-(GeneralPaperBasisIntegerDot.run v.read (mulVecRun A u).1.read).value)
  simp only [←sub_eq_add_neg,Int.natAbs_neg] at hh
  change (a*D-(GeneralPaperBasisIntegerDot.run v.read (mulVecRun A u).1.read).value).natAbs≤_
  exact hh.trans (Nat.add_le_add hProduct hDot)

theorem update_numerator {n : ℕ} (D : ℤ) (A : IntMatrix n) (u v : Vector n) (a : ℤ) (H B : ℕ)
    (hD : D.natAbs≤H) (hA : ∀ i j,((A.read i).read j).natAbs≤H)
    (hu : ∀ i,(u.read i).natAbs≤B) (hv : ∀ i,(v.read i).natAbs≤B) (ha : a.natAbs≤B) (i j : Fin n) :
    ((GeneralPaperBasisStoredStep.run D A u v a).determinant*(A.read i).read j+
      (mulVecRun A u).1.read i*(rowRun v A).1.read j).natAbs≤nextBound n H B*H+(n*H*B)*(n*B*H) := by
  have hn := determinant D A u v a H B hD hA hu hv ha
  have hAU := GeneralPaperStoredProductSize.mulVec A u H B hA hu i
  have hVA := GeneralPaperStoredProductSize.row v A B H hv hA j
  exact (Int.natAbs_add_le _ _).trans (Nat.add_le_add
    (by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hn (hA i j))
    (by rw [Int.natAbs_mul]; exact Nat.mul_le_mul hAU hVA))

theorem exact_quotient (numerator denominator : ℤ) (hd : denominator∣numerator) (B : ℕ)
    (hn : numerator.natAbs≤B) : (numerator/denominator).natAbs≤B := by
  rw [Int.natAbs_ediv_of_dvd hd]
  exact (Nat.div_le_self _ _).trans hn

end Blotto.GeneralPaperBasisUpdateOperandSize
