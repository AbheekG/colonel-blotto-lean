import Blotto.GeneralPaperMeasuredScalarPlanLifetime

/-! Constant leaves and bounded-arity record sequencing. Intermediate
plans, each join's copy activations and all parent fields coexist. A zero
child observer isolates join overhead for array/list composition. -/
namespace Blotto.GeneralPaperMeasuredRecordPlanLifetime
open GeneralPaperMeasuredBlockPlan (Plan sequence)
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def constantWindow (S : ℕ) (plan : Plan) : ℕ :=
  GeneralPaperMeasuredLayoutStorage.planFoot S plan + fields S [S,plan.work] + 64 * S

theorem constant_good (model : RationalCostModel) (S A : ℕ) (plan : Plan)
    (hA : 0 < A) (hPositive : GeneralPaperMeasuredPlanPositive.Positive plan) :
    Good model S A 2 plan (constantWindow S plan) := by
  refine ⟨hPositive,?_⟩
  intro Q hCap hWork
  have hPlan := plan_bound model S A Q plan hPositive hA hCap hWork
  have hFields := fields_bound S (natBits (cap S A Q)) [S,plan.work] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl <;> omega)
  change fields S _ ≤ 2 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S [S,plan.work] + 64 * S ≤ unit model S A Q := by omega
  have hPay := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ plan.sizes.sum + 1 by omega)
  unfold constantWindow
  nlinarith only [hPlan,hParent,hPay]

theorem tag_good (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Good model S A 2 (GeneralPaperEqualMeasuredLeafPlans.tag S)
      (constantWindow S (GeneralPaperEqualMeasuredLeafPlans.tag S)) :=
  constant_good model S A _ hA (GeneralPaperEqualMeasuredPlanPositive.tag S)

theorem empty_good (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    Good model S A 2 (GeneralPaperEqualMeasuredLeafPlans.empty S)
      (constantWindow S (GeneralPaperEqualMeasuredLeafPlans.empty S)) :=
  constant_good model S A _ hA (GeneralPaperEqualMeasuredPlanPositive.empty S)

theorem zero_good (model : RationalCostModel) (S A : ℕ) (plan : Plan)
    (hPositive : GeneralPaperMeasuredPlanPositive.Positive plan) : Good model S A 0 plan 0 := by
  refine ⟨hPositive,?_⟩
  intro Q _ _
  simp only [Nat.mul_zero,Nat.zero_mul,le_refl]

theorem join_overhead (model : RationalCostModel) (S A Q : ℕ) (left right : Plan)
    (hA : 0 < A) (hLeft : GeneralPaperMeasuredPlanPositive.Positive left)
    (hRight : GeneralPaperMeasuredPlanPositive.Positive right)
    (hCap : (GeneralPaperMeasuredBlockPlan.join S left right).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperMeasuredBlockPlan.join S left right).work ≤ Q) :
    joinWindow S A left right 0 0 ≤
      ((GeneralPaperMeasuredBlockPlan.join S left right).sizes.sum + 1) * 8 * unit model S A Q :=
  (join_good model S A 0 0 left right 0 0 hA (zero_good model S A left hLeft)
    (zero_good model S A right hRight)).2 Q hCap hWork

theorem join_window_split (S A : ℕ) (left right : Plan) (leftSpace rightSpace : ℕ) :
    joinWindow S A left right leftSpace rightSpace = leftSpace + rightSpace + joinWindow S A left right 0 0 := by
  unfold joinWindow
  omega

def sequenceWindow (S A : ℕ) : List (Plan × ℕ) → ℕ
  | [] => constantWindow S (sequence S [])
  | p :: plans => joinWindow S A p.1 (sequence S (plans.map Prod.fst)) p.2 (sequenceWindow S A plans)

theorem sequence_good (model : RationalCostModel) (S A C : ℕ) (plans : List (Plan × ℕ))
    (hA : 0 < A) (hPlans : ∀ p ∈ plans,Good model S A C p.1 p.2) :
    Good model S A (plans.length * (C + 8) + 2) (sequence S (plans.map Prod.fst)) (sequenceWindow S A plans) := by
  induction plans with
  | nil =>
    simpa only [List.map_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,sequenceWindow,
      GeneralPaperMeasuredBlockPlan.sequence,GeneralPaperEqualMeasuredLeafPlans.empty] using empty_good model S A hA
  | cons p plans ih =>
    have hp := hPlans p (List.mem_cons_self ..)
    have ht := ih (fun q hq => hPlans q (List.mem_cons_of_mem _ hq))
    have h := join_good model S A C (plans.length * (C + 8) + 2) p.1
      (sequence S (plans.map Prod.fst)) p.2 (sequenceWindow S A plans) hA hp ht
    have he : C + (plans.length * (C + 8) + 2) + 8 = (plans.length + 1) * (C + 8) + 2 := by ring
    simpa only [he,List.length_cons,List.map_cons,GeneralPaperMeasuredBlockPlan.sequence,sequenceWindow] using h

end Blotto.GeneralPaperMeasuredRecordPlanLifetime
