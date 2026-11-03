import Blotto.GeneralPaperMeasuredPlanWorkAlgebra

/-! Actual scalar measurement and reference-header arithmetic have linear
payload prices with short metadata. Empty, tag and reserved records satisfy
the same erased compositional predicate used by nested plan constructors. -/
namespace Blotto.GeneralPaperMeasuredLeafPlanWork
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem natural (model : RationalCostModel) (S A n : ℕ) (hA : 0 < A) :
    Good model S A 1 (GeneralPaperMeasuredBlockPlan.natural model S n) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.natural model S n,?_⟩
  intro hCap
  rw [natural_data] at hCap ⊢
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_one] at hCap ⊢
  have hLength : binaryWordWidth n < 2 ^ A := by unfold natBits at hCap; omega
  have hw := binaryWordWidth_le_of_lt_pow hA hLength
  have hStep := GeneralPaperStoredHeaderPreparationWork.increment_work model S A (binaryWordWidth n) (by omega)
  have hScan := GeneralPaperStoredWordLength.work S n
  have hUnit := unit_bounds model S A
  have hm := Nat.mul_le_mul_left (natBits n) (show 64 ≤ unit model S A by omega)
  have hRest : 64 * (S + 1) + GeneralPaperStoredHeaderPreparationWork.scalarBound model S A + 64 * S + 64 ≤ unit model S A := by
    unfold unit GeneralPaperStoredHeaderPreparationWork.scalarBound; omega
  change (GeneralPaperStoredWordLength.run S n).2 +
    (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2 + 64 * S + 64 ≤ _
  unfold natBits at hm ⊢
  nlinarith only [hScan,hStep,hm,hRest]

theorem rational (model : RationalCostModel) (S A : ℕ) (q : ℚ) (hA : 0 < A) :
    Good model S A 1 (GeneralPaperMeasuredBlockPlan.rational model S q) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.rational model S q,?_⟩
  intro hCap
  rw [rational_data] at hCap ⊢
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_one] at hCap ⊢
  have hw := binaryWordWidth_le_of_lt_pow hA hCap
  have hScan := GeneralPaperStoredRationalWordLength.work model S q
  have hRat := model.monotone (show binaryWordWidth (rationalWordWidth q) + 3 ≤ 8 * (A + 9) by omega)
  have hUnit := unit_bounds model S A
  have hPay := Nat.mul_le_mul_left (rationalWordWidth q) hUnit.1
  have hRest : 1024 * (S + model.rat (8 * (A + 9)) + 1) + 64 * S + 64 ≤ unit model S A := by unfold unit; omega
  change (GeneralPaperStoredRationalWordLength.run model S q).2 + 64 * S + 64 ≤ _
  nlinarith only [hScan,hRat,hPay,hRest]

theorem references_work (model : RationalCostModel) (S A count stride fixed : ℕ)
    (hCount : binaryWordWidth count ≤ A + 8) (hStride : binaryWordWidth stride ≤ A + 8)
    (hFixed : binaryWordWidth fixed ≤ A + 8) :
    (references model S A count stride fixed).work ≤ unit model S A := by
  have hA : binaryWordWidth A ≤ A + 8 := by have h := Nat.log2_le_self A; unfold binaryWordWidth; omega
  obtain ⟨bA,_,bF,bS,bC,_,b0,b1,_,b3,_⟩ := GeneralPaperStoredReferenceReadWork.slot_widths A 0 fixed stride count 0 (A + 8)
    hA (by change 1 ≤ A + 8; omega) hFixed hStride hCount (by change 1 ≤ A + 8; omega)
  change _ ≤ 8 * (A + 9) at bA bF bS bC b0 b1 b3
  have h0 := GeneralPaperNaturalScalarStep.work model S .mul stride count (8 * (A + 9)) bS bC b0
  have h1 := GeneralPaperNaturalScalarStep.work model S .add (stride * count) fixed (8 * (A + 9)) b0 bF
    (by simpa only [GeneralPaperNaturalScalarStep.Op.apply,Nat.add_comm] using b1)
  have h2 := GeneralPaperNaturalScalarStep.work model S .mul A (stride * count + fixed) (8 * (A + 9)) bA
    (by simpa only [Nat.add_comm] using b1)
    (by simpa only [GeneralPaperNaturalScalarStep.Op.apply,Nat.add_zero,Nat.add_comm] using b3)
  change (GeneralPaperNaturalScalarStep.run model S .mul stride count).2 +
    (GeneralPaperNaturalScalarStep.run model S .add (stride * count) fixed).2 +
    (GeneralPaperNaturalScalarStep.run model S .mul A (stride * count + fixed)).2 + 64 * S + 64 ≤ _
  unfold unit
  omega

theorem reserve (model : RationalCostModel) (S A arity : ℕ) (hA : 0 < A) (hArity : 0 < arity) (hArity64 : arity ≤ 64) :
    Good model S A 1 (GeneralPaperEqualMeasuredLeafPlans.reserve model S A arity) := by
  refine ⟨GeneralPaperEqualMeasuredPlanPositive.reserve model S A arity hA hArity,?_⟩
  intro _
  have hWidth := binaryWordWidth_mono hArity64
  have h64 : binaryWordWidth 64 = 7 := by decide
  have h := references_work model S A 0 0 arity (by change 1 ≤ A + 8; omega) (by change 1 ≤ A + 8; omega) (by omega)
  apply h.trans
  simpa only [Nat.mul_one,Nat.one_mul] using (Nat.mul_le_mul_right (unit model S A)
    (show 1 ≤ (GeneralPaperEqualMeasuredLeafPlans.reserve model S A arity).sizes.sum + 1 by omega))

theorem tag (model : RationalCostModel) (S A : ℕ) : Good model S A 1 (GeneralPaperEqualMeasuredLeafPlans.tag S) := by
  refine ⟨GeneralPaperEqualMeasuredPlanPositive.tag S,?_⟩
  intro _
  change 64 * S + 64 ≤ (1 + 1) * 1 * unit model S A
  have h := unit_bounds model S A
  omega

theorem empty (model : RationalCostModel) (S A : ℕ) : Good model S A 1 (GeneralPaperEqualMeasuredLeafPlans.empty S) := by
  refine ⟨GeneralPaperEqualMeasuredPlanPositive.empty S,?_⟩
  intro _
  change 64 * S + 64 ≤ (0 + 1) * 1 * unit model S A
  have h := unit_bounds model S A
  omega

end Blotto.GeneralPaperMeasuredLeafPlanWork
