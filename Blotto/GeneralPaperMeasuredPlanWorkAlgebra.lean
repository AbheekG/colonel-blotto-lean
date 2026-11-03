import Blotto.GeneralPaperStoredPreparationConstructorWork

/-! Erased compositional prices for the executed block-plan constructors.
Every bound uses the actual measured bit extent. The metadata factor does
not depend on a largest scalar payload, and each join copies its left size
list once. These predicates are proofs, not inputs to preparation. -/
namespace Blotto.GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanPositive
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def unit (model : RationalCostModel) (S A : ℕ) : ℕ :=
  4096 * (S + A + model.rat (8 * (A + 9)) + 1)

def Good (model : RationalCostModel) (S A C : ℕ) (plan : Plan) : Prop :=
  Positive plan ∧ (plan.sizes.sum < 2 ^ A → plan.work ≤ (plan.sizes.sum + 1) * C * unit model S A)

theorem unit_bounds (model : RationalCostModel) (S A : ℕ) :
    1024 ≤ unit model S A ∧ 128 * S + 2 * A + 256 ≤ unit model S A ∧
      GeneralPaperStoredHeaderPreparationWork.scalarBound model S A ≤ unit model S A := by
  unfold unit GeneralPaperStoredHeaderPreparationWork.scalarBound
  omega

theorem mono (model : RationalCostModel) (S A C D : ℕ) (plan : Plan)
    (h : Good model S A C plan) (hCD : C ≤ D) : Good model S A D plan := by
  refine ⟨h.1,fun hCap => (h.2 hCap).trans ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCD)

theorem append_work (model : RationalCostModel) (S A : ℕ) (xs ys : List ℕ)
    (hA : 0 < A) (hPos : ∀ size ∈ xs,0 < size) (hCap : xs.sum < 2 ^ A) :
    (append S xs ys).2 ≤ (xs.sum + 1) * unit model S A := by
  have hEach : ∀ size ∈ xs,natBits size ≤ A + 1 := by
    intro size hs
    have hSize := List.single_le_sum (by intro x _; exact Nat.zero_le x) size hs
    have hWidth := binaryWordWidth_le_of_lt_pow hA (hSize.trans_lt hCap)
    unfold natBits
    omega
  have hSum : (xs.map natBits).sum ≤ xs.length * (A + 1) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hh := hEach x (List.mem_cons_self ..)
      have ht := ih (fun x hx => hPos x (List.mem_cons_of_mem _ hx)) (by simp only [List.sum_cons] at hCap; omega)
        (fun x hx => hEach x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hh,ht]
  have hCount := GeneralPaperMeasuredPlanPositive.length_le_sum xs hPos
  have hUnit : A + 1 + (64 * S + 64) ≤ unit model S A := by have h := unit_bounds model S A; omega
  have hm := Nat.mul_le_mul_left (xs.length + 1) hUnit
  have hn := Nat.mul_le_mul_right (unit model S A) (Nat.add_le_add_right hCount 1)
  rw [GeneralPaperMeasuredBlockPlan.append_work]
  nlinarith only [hSum,hm,hn]

theorem join_work (model : RationalCostModel) (S A C D : ℕ) (left right : Plan)
    (hA : 0 < A) (hLeft : Good model S A C left) (hRight : Good model S A D right) :
    Good model S A (C + D + 2) (join S left right) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.join S left right hLeft.1 hRight.1,?_⟩
  intro hCap
  rw [join_sum] at hCap ⊢
  have hLCap : left.sizes.sum < 2 ^ A := by omega
  have hRCap : right.sizes.sum < 2 ^ A := by omega
  have hL := hLeft.2 hLCap
  have hR := hRight.2 hRCap
  have hAppend := append_work model S A left.sizes right.sizes hA hLeft.1 hLCap
  have hBase : 64 * S + 64 ≤ unit model S A := by have h := unit_bounds model S A; omega
  have h0 := Nat.mul_le_mul_right (C * unit model S A) (show left.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h1 := Nat.mul_le_mul_right (D * unit model S A) (show right.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h2 := Nat.mul_le_mul_right (unit model S A) (show left.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h3 := Nat.mul_le_mul_right (unit model S A) (show 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  change left.work + right.work + (append S left.sizes right.sizes).2 + 64 * S + 64 ≤ _
  nlinarith only [hL,hR,hAppend,hBase,h0,h1,h2,h3]

theorem sequence_work (model : RationalCostModel) (S A C : ℕ) (plans : List Plan)
    (hA : 0 < A) (hPlans : ∀ p ∈ plans,Good model S A C p) :
    Good model S A (plans.length * (C + 2) + 1) (sequence S plans) := by
  induction plans with
  | nil =>
    refine ⟨?_,?_⟩
    · intro x hx; cases hx
    · intro _
      change 64 * S + 64 ≤ 1 * (0 * (C + 2) + 1) * unit model S A
      have h := unit_bounds model S A
      omega
  | cons p plans ih =>
    have hp := hPlans p (List.mem_cons_self ..)
    have ht := ih (fun p hp => hPlans p (List.mem_cons_of_mem _ hp))
    have h := join_work model S A C (plans.length * (C + 2) + 1) p (sequence S plans) hA hp ht
    have he : C + (plans.length * (C + 2) + 1) + 2 = (plans.length + 1) * (C + 2) + 1 := by ring
    simpa only [he,List.length_cons,GeneralPaperMeasuredBlockPlan.sequence] using h

end Blotto.GeneralPaperMeasuredPlanWorkAlgebra
