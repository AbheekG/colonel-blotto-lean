import Blotto.GeneralPaperEpochZeroArrayPrice

/-! Initialize the eight occurrence/cell arrays of one field while retaining
its prepared plan. Every array is written once, with no query preparation,
previous-state copy or level validation pass.
-/
namespace Blotto.GeneralPaperEpochFieldInitialPrice
open GeneralPaperEpochFieldState
open GeneralPaperEpochFieldAdvancePrice (total total_mono)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) : State k × ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let po := GeneralPaperEpochZeroArrayPrice.run bits index price W s
  let qo := GeneralPaperEpochZeroArrayPrice.run bits index price W s
  let lo := GeneralPaperEpochZeroArrayPrice.run bits index price W s
  let mo := GeneralPaperEpochZeroArrayPrice.run bits index price W s
  let pc := GeneralPaperEpochZeroArrayPrice.run bits index price W plan.pCells.partition.count
  let qc := GeneralPaperEpochZeroArrayPrice.run bits index price W plan.qCells.partition.count
  let lc := GeneralPaperEpochZeroArrayPrice.run bits index price W plan.lambdaCells.partition.count
  let mc := GeneralPaperEpochZeroArrayPrice.run bits index price W plan.muCells.partition.count
  (⟨plan,po.1,qo.1,lo.1,mo.1,pc.1,qc.1,lc.1,mc.1⟩,total po.2 qo.2 lo.2 mo.2 pc.2 qc.2 lc.2 mc.2+256*W)

def profile (price : ℕ → ℕ) (W B : ℕ) : ℕ := 8*GeneralPaperEpochZeroArrayPrice.profile price W B+256*W
def arithmeticProfile (B : ℕ) : ℕ := 8*GeneralPaperEpochZeroArrayPrice.arithmeticProfile B+256

theorem data {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) :
    (run bits index price W plan).1=initial plan := by
  unfold run initial
  dsimp only
  simp only [GeneralPaperEpochZeroArrayPrice.data]

theorem retained_plan {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) :
    (run bits index price W plan).1.plan=plan := rfl

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (W B : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k)
    (hs : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : plan.pCells.partition.count≤B) (hq : plan.qCells.partition.count≤B)
    (hl : plan.lambdaCells.partition.count≤B) (hm : plan.muCells.partition.count≤B) :
    (run true (fun w => w) price W plan).2≤profile price W B := by
  have bound (n : ℕ) (hn : n≤B) : (GeneralPaperEpochZeroArrayPrice.run true (fun w => w) price W n).2≤
      GeneralPaperEpochZeroArrayPrice.profile price W B :=
    (GeneralPaperEpochZeroArrayPrice.bit_work price W n).trans (GeneralPaperEpochZeroArrayPrice.profile_mono price W n B hn)
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (bound _ hs) (bound _ hs) (bound _ hs) (bound _ hs) (bound _ hp) (bound _ hq) (bound _ hl) (bound _ hm)) (256*W)
  exact h.trans_eq (by unfold profile total; ring)

theorem arithmetic_work {k : ℕ} (B : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k)
    (hs : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : plan.pCells.partition.count≤B) (hq : plan.qCells.partition.count≤B)
    (hl : plan.lambdaCells.partition.count≤B) (hm : plan.muCells.partition.count≤B) :
    (run false (fun _ => 1) (fun _ => 1) 1 plan).2≤arithmeticProfile B := by
  have bound (n : ℕ) (hn : n≤B) : (GeneralPaperEpochZeroArrayPrice.run false (fun _ => 1) (fun _ => 1) 1 n).2≤
      GeneralPaperEpochZeroArrayPrice.arithmeticProfile B :=
    (GeneralPaperEpochZeroArrayPrice.arithmetic_work n).trans (GeneralPaperEpochZeroArrayPrice.arithmetic_profile_mono n B hn)
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (bound _ hs) (bound _ hs) (bound _ hs) (bound _ hs) (bound _ hp) (bound _ hq) (bound _ hl) (bound _ hm)) 256
  exact h.trans_eq (by unfold arithmeticProfile total; ring)

end Blotto.GeneralPaperEpochFieldInitialPrice
