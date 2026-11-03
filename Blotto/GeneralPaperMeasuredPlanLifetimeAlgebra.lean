import Blotto.GeneralPaperSelectedReferenceCollectionLifetime

/-! Compositional lifetime bounds for actual measured plans. A saved price
is charged by its encoded width. Left-only size-list copying owns each left
head once and shares the right/output suffix. The predicates and bounds
are erased observers, never supplied to the executing constructor. -/
namespace Blotto.GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredBlockPlan (Plan append join sequence)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanPositive (Positive)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def unit (model : RationalCostModel) (S A Q : ℕ) : ℕ :=
  4194304 * (S + A + model.rat (8 * (A + 9)) + natBits (cap S A Q) + 1)

def Good (model : RationalCostModel) (S A C : ℕ) (plan : Plan) (space : ℕ) : Prop :=
  Positive plan ∧ ∀ Q,plan.sizes.sum < 2 ^ A → plan.work ≤ Q →
    space ≤ (plan.sizes.sum + 1) * C * unit model S A Q

theorem unit_bounds (model : RationalCostModel) (S A Q : ℕ) :
    256 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A +
      4096 * (S + A + natBits (cap S A Q) + 1) ≤ unit model S A Q := by
  unfold unit GeneralPaperMeasuredPlanWorkAlgebra.unit
  omega

theorem mono (model : RationalCostModel) (S A C D : ℕ) (plan : Plan) (space : ℕ)
    (h : Good model S A C plan space) (hCD : C ≤ D) : Good model S A D plan space := by
  refine ⟨h.1,fun Q hCap hWork => (h.2 Q hCap hWork).trans ?_⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hCD)

theorem price_word (S A Q price : ℕ) (hPrice : price ≤ Q) : natBits price ≤ natBits (cap S A Q) :=
  Nat.add_le_add_left (binaryWordWidth_mono (hPrice.trans (by unfold cap; omega))) 1

theorem plan_bound (model : RationalCostModel) (S A Q : ℕ) (plan : Plan)
    (hPos : Positive plan) (hA : 0 < A) (hCap : plan.sizes.sum < 2 ^ A) (hWork : plan.work ≤ Q) :
    GeneralPaperMeasuredLayoutStorage.planFoot S plan ≤ (plan.sizes.sum + 1) * unit model S A Q := by
  have h := GeneralPaperMeasuredLayoutStorage.plan_bound S A plan hPos hA hCap Q hWork
  have hQ := price_word S A Q Q le_rfl
  have hUnit := unit_bounds model S A Q
  have hStep : A + 2 * S + 1 + natBits Q + 129 * S ≤ unit model S A Q := by omega
  have hPay := Nat.mul_le_mul_left (plan.sizes.sum + 1) hStep
  unfold GeneralPaperMeasuredLayoutStorage.planBound at h
  nlinarith only [h,hPay,Nat.zero_le (plan.sizes.sum * (natBits Q + 129 * S))]

def appendFrames (S A : ℕ) (xs ys : List ℕ) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.liftFrames S A natBits (fun values => (append S values ys).2) xs

theorem append_bound (model : RationalCostModel) (S A Q : ℕ) (xs ys : List ℕ)
    (hA : 0 < A) (hPos : ∀ x ∈ xs,0 < x) (hCap : xs.sum < 2 ^ A) (hWork : (append S xs ys).2 ≤ Q) :
    appendFrames S A xs ys ≤ (xs.sum + 1) * unit model S A Q := by
  have hFrames := GeneralPaperUnifiedInstallationLifetime.lift_frames_bound S A Q natBits
    (fun values => (append S values ys).2) xs (fun x values => by dsimp only [append]; omega) hWork
  have hSum := sum_bound natBits (A + 1) xs (by
    intro x hx
    have h := binaryWordWidth_le_of_lt_pow hA ((List.single_le_sum (fun y _ => Nat.zero_le y) x hx).trans_lt hCap)
    unfold natBits; omega)
  have hCount := GeneralPaperMeasuredPlanPositive.length_le_sum xs hPos
  have hUnit := unit_bounds model S A Q
  have hStep : A + 1 + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A Q ≤ unit model S A Q := by
    unfold GeneralPaperUnifiedInstallationLifetime.liftFrameBound
    omega
  have hPay := Nat.mul_le_mul_left (xs.sum + 1) hStep
  have hCountPay := Nat.mul_le_mul_right (A + 1 + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A Q)
    (Nat.add_le_add_right hCount 1)
  unfold appendFrames
  nlinarith only [hFrames,hSum,hPay,hCountPay]

theorem append_shared_suffix (S : ℕ) (xs ys : List ℕ) : (append S xs ys).1.drop xs.length = ys := by
  rw [GeneralPaperMeasuredBlockPlan.append_data]
  exact List.drop_left

def joinControls (S A : ℕ) (left right : Plan) : List ℕ :=
  [S,A,left.work,right.work,(append S left.sizes right.sizes).2,left.work + right.work,
    left.work + right.work + (append S left.sizes right.sizes).2,(join S left right).work]

def joinWindow (S A : ℕ) (left right : Plan) (leftSpace rightSpace : ℕ) : ℕ :=
  leftSpace + rightSpace + appendFrames S A left.sizes right.sizes +
    GeneralPaperMeasuredLayoutStorage.planFoot S left + GeneralPaperMeasuredLayoutStorage.planFoot S right +
    GeneralPaperMeasuredLayoutStorage.planFoot S (join S left right) + fields S (joinControls S A left right) + 128 * S

theorem join_good (model : RationalCostModel) (S A C D : ℕ) (left right : Plan) (leftSpace rightSpace : ℕ)
    (hA : 0 < A) (hLeft : Good model S A C left leftSpace) (hRight : Good model S A D right rightSpace) :
    Good model S A (C + D + 8) (join S left right) (joinWindow S A left right leftSpace rightSpace) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.join S left right hLeft.1 hRight.1,?_⟩
  intro Q hCap hWork
  have hWhole := hWork
  change left.work + right.work + (append S left.sizes right.sizes).2 + 64 * S + 64 ≤ Q at hWork
  rw [GeneralPaperMeasuredBlockPlan.join_sum] at hCap ⊢
  have hLCap : left.sizes.sum < 2 ^ A := by omega
  have hRCap : right.sizes.sum < 2 ^ A := by omega
  have hL := hLeft.2 Q hLCap (by omega)
  have hR := hRight.2 Q hRCap (by omega)
  have hAppend := append_bound model S A Q left.sizes right.sizes hA hLeft.1 hLCap (by omega)
  have hLP := plan_bound model S A Q left hLeft.1 hA hLCap (by omega)
  have hRP := plan_bound model S A Q right hRight.1 hA hRCap (by omega)
  have hJP := plan_bound model S A Q (join S left right)
    (GeneralPaperMeasuredPlanPositive.join S left right hLeft.1 hRight.1) hA (by rw [GeneralPaperMeasuredBlockPlan.join_sum]; exact hCap) hWhole
  rw [GeneralPaperMeasuredBlockPlan.join_sum] at hJP
  have hFields := fields_bound S (natBits (cap S A Q)) (joinControls S A left right) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [joinControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S (joinControls S A left right) + 128 * S ≤ unit model S A Q := by omega
  have h0 := Nat.mul_le_mul_right (C * unit model S A Q)
    (show left.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h1 := Nat.mul_le_mul_right (D * unit model S A Q)
    (show right.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h2 := Nat.mul_le_mul_right (unit model S A Q)
    (show left.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h3 := Nat.mul_le_mul_right (unit model S A Q)
    (show right.sizes.sum + 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  have h4 := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ left.sizes.sum + right.sizes.sum + 1 by omega)
  unfold joinWindow
  nlinarith only [hL,hR,hAppend,hLP,hRP,hJP,hParent,h0,h1,h2,h3,h4]

end Blotto.GeneralPaperMeasuredPlanLifetimeAlgebra
