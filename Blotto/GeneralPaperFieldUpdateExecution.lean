import Blotto.GeneralPaperFieldAdvanceEnvelope

/-! Each field generates its eight deltas once and advances all eight level
arrays once. Snapshot, plan and choices are retained inputs. Data equality
identifies this composition with the actual native field update.
-/
namespace Blotto.GeneralPaperFieldUpdateExecution
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan) : State k × ℕ :=
  let primitive := if bits then price else fun _ => 1
  let delta := GeneralPaperFieldDeltaExecution.run bits index primitive W mesh state snapshot choice
  let updated := GeneralPaperEpochFieldAdvancePrice.run bits index primitive W state delta.1
  (updated.1,delta.2+updated.2+64*W)

theorem data {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index price W mesh state snapshot choice).1=advance state (generate state snapshot choice).1 := by
  unfold run
  dsimp only
  rw [GeneralPaperEpochFieldAdvancePrice.data,GeneralPaperFieldDeltaExecution.data bits index _ W mesh _ _ _ hMesh]

theorem retained_plan {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan) : (run bits index price W mesh state snapshot choice).1.plan=state.plan := rfl

def profile (price : ℕ → ℕ) (W m lambda k Qv B : ℕ) : ℕ :=
  GeneralPaperFieldDeltaPrice.uniformProfile price W m lambda k Qv B+
    GeneralPaperFieldAdvanceEnvelope.profile price W m lambda k Qv B+64*W

def arithmeticProfile (k B : ℕ) : ℕ :=
  GeneralPaperFieldDeltaPrice.uniformArithmeticProfile k B+GeneralPaperFieldAdvanceEnvelope.arithmeticProfile B+64

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv B mesh : ℕ)
    (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : ∀ learner,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv
      (GeneralPaperCatalogueOccurrenceHistory.block learner snapshot).cdf)
    (hSafe : GeneralPaperDeltaPlanBounds.PlanSafe lambda state.plan)
    (hState : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) (hPositive : Positive snapshot) (hCoherent : Coherent snapshot)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    (run true (fun w => w) price W mesh state snapshot choice).2≤profile price W m lambda k Qv B := by
  let delta := GeneralPaperFieldDeltaExecution.run true (fun w => w) price W mesh state snapshot choice
  have hd := (GeneralPaperFieldDeltaPrice.bit_work price hMono W m lambda Qv mesh state snapshot choice hMesh hGood hSafe).trans
    (GeneralPaperFieldDeltaPrice.profile_bound price W m lambda Qv B state hS hp hq hl hm)
  have hDelta := GeneralPaperFieldDeltaExecution.returned_bound true (fun w => w) price W mesh state snapshot choice hMesh hPositive hCoherent
  have ha := (GeneralPaperEpochFieldAdvancePrice.bit_work price hMono W m lambda Qv state delta.1 hState hDelta).trans
    (GeneralPaperFieldAdvanceEnvelope.bound price W m lambda Qv B state hS hp hq hl hm)
  exact Nat.add_le_add_right (Nat.add_le_add hd ha) _

theorem arithmetic_work {k : ℕ} (price : ℕ → ℕ) (B mesh : ℕ) (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    (run false (fun _ => 1) price 1 mesh state snapshot choice).2≤arithmeticProfile k B := by
  let delta := GeneralPaperFieldDeltaExecution.run false (fun _ => 1) (fun _ => 1) 1 mesh state snapshot choice
  have hd := (GeneralPaperFieldDeltaPrice.arithmetic_work mesh state snapshot choice).trans
    (GeneralPaperFieldDeltaPrice.arithmetic_profile_bound B state hS hp hq hl hm)
  have ha := (GeneralPaperEpochFieldAdvancePrice.arithmetic_work state delta.1).trans
    (GeneralPaperFieldAdvanceEnvelope.arithmetic_bound B state hS hp hq hl hm)
  exact Nat.add_le_add_right (Nat.add_le_add hd ha) _

theorem same_data {k : ℕ} (price : ℕ → ℕ) (W mesh : ℕ) (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run true (fun w => w) price W mesh state snapshot choice).1=(run false (fun _ => 1) price 1 mesh state snapshot choice).1 := by
  rw [data true (fun w => w) price W mesh _ _ _ hMesh,data false (fun _ => 1) price 1 mesh _ _ _ hMesh]

end Blotto.GeneralPaperFieldUpdateExecution
