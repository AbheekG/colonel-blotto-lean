import Blotto.GeneralPaperMeasuredArrayPlanWork

/-! Complete counted-list plan work includes each actual measurement,
left size-list copy, counter increment, header arithmetic and final join.
The header's reserved area pays for per-item control even for empty unit
payloads. Bounds are linear in total measured area. -/
namespace Blotto.GeneralPaperMeasuredListPlanWork
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanWorkAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem body_work {α : Type*} (model : RationalCostModel) (S A C : ℕ) (measure : α → Plan) (xs : List α)
    (hA : 0 < A) (hGood : ∀ x ∈ xs,Good model S A C (measure x))
    (hWidth : binaryWordWidth xs.length ≤ A + 8)
    (hCap : (xs.map (fun x => (measure x).sizes.sum)).sum < 2 ^ A) :
    (GeneralPaperMeasuredListBlockPlan.body model S measure xs).work ≤
      ((xs.map (fun x => (measure x).sizes.sum)).sum + xs.length + 1) * (C + 3) * unit model S A := by
  induction xs with
  | nil =>
    change 64 * S + 64 ≤ (0 + 0 + 1) * (C + 3) * unit model S A
    have hU := unit_bounds model S A
    nlinarith only [hU.2.1,Nat.zero_le (C * unit model S A)]
  | cons x xs ih =>
    have hh := hGood x (List.mem_cons_self ..)
    have hTailGood := fun y hy => hGood y (List.mem_cons_of_mem x hy)
    have hHeadCap : (measure x).sizes.sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hTailCap : (xs.map (fun y => (measure y).sizes.sum)).sum < 2 ^ A := by simp only [List.map_cons,List.sum_cons] at hCap; omega
    have hTailWidth := (binaryWordWidth_mono (show xs.length ≤ (x :: xs).length by simp only [List.length_cons]; omega)).trans hWidth
    have ht := ih hTailGood hTailWidth hTailCap
    have hHead := hh.2 hHeadCap
    have hAppend := GeneralPaperMeasuredPlanWorkAlgebra.append_work model S A (measure x).sizes
      (GeneralPaperMeasuredListBlockPlan.body model S measure xs).sizes hA hh.1 hHeadCap
    have hStep := GeneralPaperStoredHeaderPreparationWork.increment_work model S A xs.length hTailWidth
    have hU := unit_bounds model S A
    have hStepU := hStep.trans hU.2.2
    have hBase : 64 * S + 64 ≤ unit model S A := by omega
    simp only [GeneralPaperMeasuredListBlockPlan.body,GeneralPaperMeasuredListBlockPlan.body_count,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hHead,hAppend,ht,hStepU,hBase,Nat.zero_le ((measure x).sizes.sum * unit model S A)]

theorem area {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan) (xs : List α) :
    (GeneralPaperMeasuredListBlockPlan.run model S A stride fixed measure xs).sizes.sum =
      A * (stride * xs.length + fixed) + (xs.map (fun x => (measure x).sizes.sum)).sum :=
  GeneralPaperMeasuredListBlockPlan.sum model S A stride fixed measure (fun x => (measure x).sizes.sum) xs (fun _ _ => rfl)

theorem list {α : Type*} (model : RationalCostModel) (S A C stride fixed : ℕ) (measure : α → Plan) (xs : List α)
    (hA : 0 < A) (hStride : 0 < stride) (hStride64 : stride ≤ 64) (hFixed : 0 < fixed) (hFixed64 : fixed ≤ 64)
    (hGood : ∀ x ∈ xs,Good model S A C (measure x)) :
    Good model S A (C + 8) (GeneralPaperMeasuredListBlockPlan.run model S A stride fixed measure xs) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.list model S A stride fixed measure xs hA (by omega) (fun x hx => (hGood x hx).1),?_⟩
  intro hCap
  rw [area] at hCap ⊢
  let P := (xs.map (fun x => (measure x).sizes.sum)).sum
  have hArea : A * (stride * xs.length + fixed) + P < 2 ^ A := hCap
  have hN : xs.length ≤ A * (stride * xs.length + fixed) := by
    have hs := Nat.mul_le_mul_right xs.length hStride
    have ha := Nat.mul_le_mul_right (stride * xs.length + fixed) hA
    nlinarith only [hs,ha]
  have hHeader : A * (stride * xs.length + fixed) < 2 ^ A := by omega
  have hCount := binaryWordWidth_le_of_lt_pow hA (show xs.length < 2 ^ A by omega)
  have hBody := body_work model S A C measure xs hA hGood (by omega) (by change P < 2 ^ A; omega)
  have hStrideW := binaryWordWidth_mono hStride64
  have hFixedW := binaryWordWidth_mono hFixed64
  have h64 : binaryWordWidth 64 = 7 := by decide
  have hHeaderWork := GeneralPaperMeasuredLeafPlanWork.references_work model S A xs.length stride fixed (by omega) (by omega) (by omega)
  have hAppend := GeneralPaperMeasuredArrayPlanWork.singleton_append model S A (A * (stride * xs.length + fixed))
    (GeneralPaperMeasuredListBlockPlan.body model S measure xs).sizes hA hHeader
  have hBase : 64 * S + 64 ≤ unit model S A := by have h := unit_bounds model S A; omega
  have hm := Nat.mul_le_mul_right ((C + 3) * unit model S A)
    (show P + xs.length + 1 ≤ A * (stride * xs.length + fixed) + P + 1 by omega)
  have hSlack := Nat.mul_le_mul_right (unit model S A)
    (show 3 ≤ 5 * (A * (stride * xs.length + fixed) + P + 1) by omega)
  unfold GeneralPaperMeasuredListBlockPlan.run GeneralPaperMeasuredBlockPlan.join
  simp only [GeneralPaperMeasuredListBlockPlan.body_count,GeneralPaperMeasuredBlockPlan.references_data]
  change (references model S A xs.length stride fixed).work +
    (GeneralPaperMeasuredListBlockPlan.body model S measure xs).work +
    (append S [A * (stride * xs.length + fixed)] (GeneralPaperMeasuredListBlockPlan.body model S measure xs).sizes).2 + 64 * S + 64 ≤ _
  change (GeneralPaperMeasuredListBlockPlan.body model S measure xs).work ≤ (P + xs.length + 1) * (C + 3) * unit model S A at hBody
  dsimp only [P] at hBody hm hSlack
  nlinarith only [hBody,hHeaderWork,hAppend,hBase,hm,hSlack]

end Blotto.GeneralPaperMeasuredListPlanWork
