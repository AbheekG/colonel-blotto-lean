import Blotto.BinaryWordStoreWork
import Blotto.BinaryTraceDepth
import Blotto.BinaryTracePlanMeasured

/-! Carry counting and physical seed-tree construction are executed once,
with data, the old allocation trace and source work returned together.
Observer evaluation and native reference/allocator prices remain separate. -/

namespace Blotto.BinaryWordStoreMeasured
open BinarySeedPreparationSpace BinarySeedLookupTree BinaryTraceDepth
open BinaryTracePlanMeasured (Plan)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def carryAt : List Bool → ℕ → (List Bool × Trace) × ℕ
  | [],depth => (([true],[.frames (depth+1),.listAllocation 1,.arrayAllocation 4]),4)
  | false::rest,depth => ((true::rest,[.frames (depth+1),.listAllocation 1,.arrayAllocation 4]),4)
  | true::rest,depth =>
      let later := carryAt rest (depth+1)
      ((false::later.1.1,.frames (depth+1)::.listAllocation 1::.arrayAllocation 4::later.1.2),later.2+4)

theorem carryAt_erases (bits : List Bool) (depth : ℕ) :
    (carryAt bits depth).1 = ((BinaryWordStoreLifetime.carryWithTrace bits).1,
      under depth (BinaryWordStoreLifetime.carryWithTrace bits).2) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit with
    | false => rfl
    | true =>
        simp only [carryAt,BinaryWordStoreLifetime.carryWithTrace,ih,under_append,under_compose]
        rfl

def carry (bits : List Bool) : (List Bool × Trace) × ℕ := carryAt bits 0

theorem carry_erases (bits : List Bool) :
    (carry bits).1 = BinaryWordStoreLifetime.carryWithTrace bits := by
  rw [carry,carryAt_erases,under_zero]

theorem carryAt_work (bits : List Bool) (depth : ℕ) :
    (carryAt bits depth).2 = (BinaryWordStoreWork.carryWithWork bits).2 := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [carryAt,BinaryWordStoreWork.carryWithWork,ih]

theorem carry_work (bits : List Bool) :
    (carry bits).2 = (BinaryWordStoreWork.carryWithWork bits).2 := carryAt_work bits 0

def countAt {α : Type*} : List α → List Bool → ℕ → (List Bool × Trace) × ℕ
  | [],counter,depth => ((counter,[.frames (depth+1),.arrayAllocation 4]),2)
  | _::rest,counter,depth =>
      let advanced := carryAt counter (depth+2)
      let later := countAt rest advanced.1.1 (depth+1)
      ((later.1.1,.frames (depth+2)::.arrayAllocation 4::(advanced.1.2++later.1.2)),
        advanced.2+later.2+1)

theorem countAt_erases {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countAt items counter depth).1 = ((BinaryWordStoreLifetime.countWithTrace items counter).1,
      under depth (BinaryWordStoreLifetime.countWithTrace items counter).2) := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [countAt,BinaryWordStoreLifetime.countWithTrace,carryAt_erases,ih,
        under_append,under_compose,List.append_assoc]
      rfl

theorem countAt_data {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countAt items counter depth).1.1 = (BinaryWordStoreLifetime.countWithTrace items counter).1 := by
  have h := congrArg (fun d : List Bool × Trace => d.1) (countAt_erases items counter depth)
  exact h

def count {α : Type*} (items : List α) (counter : List Bool) : (List Bool × Trace) × ℕ :=
  countAt items counter 0

theorem count_erases {α : Type*} (items : List α) (counter : List Bool) :
    (count items counter).1 = BinaryWordStoreLifetime.countWithTrace items counter := by
  rw [count,countAt_erases,under_zero]

theorem countAt_work {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countAt items counter depth).2 = (BinaryWordStoreWork.countWithWork items counter).2 := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      simp only [countAt,BinaryWordStoreWork.countWithWork,ih,carryAt_work,carryAt_erases,
        BinaryWordStoreWork.carry_state]

theorem count_work {α : Type*} (items : List α) (counter : List Bool) :
    (count items counter).2 = (BinaryWordStoreWork.countWithWork items counter).2 := countAt_work items counter 0

theorem count_data {α : Type*} (items : List α) (counter : List Bool) :
    (count items counter).1.1 = (BinaryWordStoreLifetime.countWithTrace items counter).1 :=
  congrArg (fun d : List Bool × Trace => d.1) (count_erases items counter)

def buildPlanAt : (ruler : List Bool) → List Bool → ℕ → ((Tree ruler.length × List Bool) × Plan) × ℕ
  | [],[],depth => (((.leaf false,[]),.block [.frames (depth+1),.arrayAllocation 8]),6)
  | [],bit::rest,depth => (((.leaf bit,rest),.block [.frames (depth+1),.arrayAllocation 8]),6)
  | _::ruler,seed,depth =>
      let left := buildPlanAt ruler seed (depth+1)
      let right := buildPlanAt ruler left.1.1.2 (depth+1)
      (((.branch left.1.1.1 right.1.1.1,right.1.1.2),
        .join (.block [.frames (depth+1),.arrayAllocation 8]) (.join left.1.2 right.1.2)),left.2+right.2+6)

theorem buildPlanAt_data (ruler seed : List Bool) (depth : ℕ) :
    (buildPlanAt ruler seed depth).1.1 = (BinaryWordStoreLifetime.buildWithTrace ruler seed).1 := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> rfl
  | cons cell ruler ih => simp only [buildPlanAt,BinaryWordStoreLifetime.buildWithTrace,ih]

theorem buildPlanAt_trace (ruler seed : List Bool) (depth : ℕ) :
    BinaryTracePlanMeasured.denote (buildPlanAt ruler seed depth).1.2 =
      under depth (BinaryWordStoreLifetime.buildWithTrace ruler seed).2 := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> rfl
  | cons cell ruler ih =>
      simp only [buildPlanAt,BinaryTracePlanMeasured.denote,BinaryWordStoreLifetime.buildWithTrace,
        ih,buildPlanAt_data,under_append,under_compose,List.append_assoc]
      rfl

theorem buildPlanAt_work (ruler seed : List Bool) (depth : ℕ) :
    (buildPlanAt ruler seed depth).2 = (BinaryWordStoreWork.buildWithWork ruler seed).2 := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> rfl
  | cons cell ruler ih =>
      simp only [buildPlanAt,BinaryWordStoreWork.buildWithWork,ih,buildPlanAt_data,
        BinaryWordStoreWork.build_state]

def buildAtMeasured (ruler seed : List Bool) (depth : ℕ) :
    (((Tree ruler.length × List Bool) × Trace) × ℕ) × ℕ :=
  let built := buildPlanAt ruler seed depth
  let emitted := BinaryTracePlanMeasured.emit built.1.2 []
  (((built.1.1,emitted.1),built.2),emitted.2)

def buildAt (ruler seed : List Bool) (depth : ℕ) : ((Tree ruler.length × List Bool) × Trace) × ℕ :=
  (buildAtMeasured ruler seed depth).1

theorem buildAtMeasured_compat (ruler seed : List Bool) (depth : ℕ) :
    (buildAtMeasured ruler seed depth).1 = buildAt ruler seed depth := rfl

theorem buildAt_erases (ruler seed : List Bool) (depth : ℕ) :
    (buildAt ruler seed depth).1 = ((BinaryWordStoreLifetime.buildWithTrace ruler seed).1,
      under depth (BinaryWordStoreLifetime.buildWithTrace ruler seed).2) := by
  simp only [buildAt,buildAtMeasured,BinaryTracePlanMeasured.emit_data,List.append_nil,buildPlanAt_data,buildPlanAt_trace]

def build (ruler seed : List Bool) : ((Tree ruler.length × List Bool) × Trace) × ℕ := buildAt ruler seed 0

theorem build_erases (ruler seed : List Bool) :
    (build ruler seed).1 = BinaryWordStoreLifetime.buildWithTrace ruler seed := by
  rw [build,buildAt_erases,under_zero]

theorem buildAt_work (ruler seed : List Bool) (depth : ℕ) :
    (buildAt ruler seed depth).2 = (BinaryWordStoreWork.buildWithWork ruler seed).2 := buildPlanAt_work ruler seed depth

theorem build_work (ruler seed : List Bool) :
    (build ruler seed).2 = (BinaryWordStoreWork.buildWithWork ruler seed).2 := buildAt_work ruler seed 0

def preparePlan (seed : List Bool) : (Store × Plan) × ℕ :=
  let ruler := countAt seed [] 2
  let built := buildPlanAt ruler.1.1 seed 2
  let width := ruler.1.1.length
  let planned := Plan.join (.block [.frames (width+4),.arrayAllocation 8])
    (.join (.block ruler.1.2) built.1.2)
  ((⟨width,⟨ruler.1.1,rfl⟩,built.1.1.1⟩,planned),ruler.2+built.2+width+4)

def prepareMeasured (seed : List Bool) : ((Store × Trace) × ℕ) × ℕ :=
  let planned := preparePlan seed
  let emitted := BinaryTracePlanMeasured.emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

def prepare (seed : List Bool) : (Store × Trace) × ℕ := (prepareMeasured seed).1

theorem prepareMeasured_compat (seed : List Bool) : (prepareMeasured seed).1 = prepare seed := rfl

theorem prepare_erases (seed : List Bool) :
    (prepare seed).1 = BinaryWordStoreLifetime.prepareWithTrace seed := by
  let assemble (ruler : List Bool × Trace) : Store × Trace :=
    let built := BinaryWordStoreLifetime.buildWithTrace ruler.1 seed
    (⟨ruler.1.length,⟨ruler.1,rfl⟩,built.1.1⟩,
      [.frames (ruler.1.length+4),.arrayAllocation 8]++ruler.2++under 2 built.2)
  simp only [prepare,prepareMeasured,preparePlan,BinaryWordStoreLifetime.prepareWithTrace,BinaryTracePlanMeasured.emit_data,
    BinaryTracePlanMeasured.denote,List.append_nil,buildPlanAt_data,buildPlanAt_trace,
    List.append_assoc]
  change assemble (countAt seed [] 2).1 = assemble
    ((BinaryWordStoreLifetime.countWithTrace seed []).1,
      under 2 (BinaryWordStoreLifetime.countWithTrace seed []).2)
  exact congrArg assemble (countAt_erases seed [] 2)

theorem prepare_work (seed : List Bool) :
    (prepare seed).2 = (BinaryWordStoreWork.prepareWithWork seed).2 := by
  have hc := (countAt_data seed [] 2).trans (BinaryWordStoreWork.count_state seed []).symm
  have hb := congrArg (fun ruler => (BinaryWordStoreWork.buildWithWork ruler seed).2) hc
  have hw := congrArg List.length hc
  simp only [prepare,prepareMeasured,preparePlan,BinaryWordStoreWork.prepareWithWork,countAt_work,buildPlanAt_work]
  rw [hb,hw]

theorem prepare_bound (seed : List Bool) : (prepare seed).2 ≤ 34*seed.length+13 := by
  rw [prepare_work]
  exact BinaryWordStoreWork.prepare_work seed

theorem carryAt_trace_length (bits : List Bool) (depth : ℕ) :
    (carryAt bits depth).1.2.length = 3*BinaryCarryCounter.carryCells bits := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [carryAt,BinaryCarryCounter.carryCells,List.length_cons,List.length_nil,ih] <;> omega

theorem carryAt_trace_work (bits : List Bool) (depth : ℕ) :
    (carryAt bits depth).1.2.length ≤ (carryAt bits depth).2 := by
  rw [carryAt_trace_length,carryAt_work,BinaryWordStoreWork.carry_work]
  omega

theorem carryAt_frames (bits : List Bool) (depth : ℕ) :
    framePeak (carryAt bits depth).1.2 ≤ depth+bits.length+1 := by
  have h := (BinaryWordStoreLifetime.carryWithTrace_bounds bits).2
  have hu := framePeak_under depth (BinaryWordStoreLifetime.carryWithTrace bits).2
  rw [carryAt_erases]
  dsimp only
  omega

theorem countAt_trace_work {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countAt items counter depth).1.2.length ≤ 2*(countAt items counter depth).2 := by
  induction items generalizing counter depth with
  | nil => simp [countAt]
  | cons item rest ih =>
      have hc := carryAt_trace_work counter (depth+2)
      have hl := ih (carryAt counter (depth+2)).1.1 (depth+1)
      simp only [countAt,List.length_cons,List.length_append]
      omega

theorem countAt_frames {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    framePeak (countAt items counter depth).1.2 ≤ depth+2*items.length+counter.length+3 := by
  have h := (BinaryWordStoreLifetime.countWithTrace_bounds items counter).2
  have hu := framePeak_under depth (BinaryWordStoreLifetime.countWithTrace items counter).2
  rw [countAt_erases]
  dsimp only
  omega

theorem buildPlanAt_budget (ruler seed : List Bool) (depth : ℕ) :
    BinaryTracePlanMeasured.payload (buildPlanAt ruler seed depth).1.2+
      BinaryTracePlanMeasured.nodes (buildPlanAt ruler seed depth).1.2 ≤
        (buildPlanAt ruler seed depth).2 := by
  induction ruler generalizing seed depth with
  | nil => cases seed <;> simp [buildPlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes]
  | cons cell ruler ih =>
      have hl := ih seed (depth+1)
      have hr := ih (buildPlanAt ruler seed (depth+1)).1.1.2 (depth+1)
      simp only [buildPlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
        List.length_cons,List.length_nil]
      omega

theorem buildAt_emit_work (ruler seed : List Bool) (depth : ℕ) :
    (BinaryTracePlanMeasured.emit (buildPlanAt ruler seed depth).1.2 []).2 ≤
      4*(buildAt ruler seed depth).2 :=
  BinaryTracePlanMeasured.emit_work_bound _ _ _ (buildPlanAt_budget ruler seed depth)

theorem buildAtMeasured_emission (ruler seed : List Bool) (depth : ℕ) :
    (buildAtMeasured ruler seed depth).2 ≤ 4*(buildAtMeasured ruler seed depth).1.2 :=
  buildAt_emit_work ruler seed depth

theorem buildAtMeasured_source_plus_emission (ruler seed : List Bool) (depth : ℕ) :
    (buildAtMeasured ruler seed depth).1.2+(buildAtMeasured ruler seed depth).2 ≤
      5*(buildAtMeasured ruler seed depth).1.2 := by
  have h := buildAtMeasured_emission ruler seed depth
  omega

theorem buildAt_frames (ruler seed : List Bool) (depth : ℕ) :
    framePeak (buildAt ruler seed depth).1.2 ≤ depth+ruler.length+1 := by
  have h := (BinaryWordStoreLifetime.buildWithTrace_bounds ruler seed).2
  have hu := framePeak_under depth (BinaryWordStoreLifetime.buildWithTrace ruler seed).2
  rw [buildAt_erases]
  dsimp only
  omega

theorem preparePlan_budget (seed : List Bool) :
    BinaryTracePlanMeasured.payload (preparePlan seed).1.2+
      BinaryTracePlanMeasured.nodes (preparePlan seed).1.2 ≤ 2*(preparePlan seed).2 := by
  have hc := countAt_trace_work seed [] 2
  have hb := buildPlanAt_budget (countAt seed [] 2).1.1 seed 2
  simp only [preparePlan,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
    List.length_cons,List.length_nil]
  omega

theorem prepare_emit_work (seed : List Bool) :
    (BinaryTracePlanMeasured.emit (preparePlan seed).1.2 []).2 ≤ 8*(prepare seed).2 := by
  have h := BinaryTracePlanMeasured.emit_work_bound _ [] _ (preparePlan_budget seed)
  change _ ≤ 8*(preparePlan seed).2
  omega

theorem prepareMeasured_emission (seed : List Bool) :
    (prepareMeasured seed).2 ≤ 8*(prepareMeasured seed).1.2 := prepare_emit_work seed

theorem prepareMeasured_source_plus_emission (seed : List Bool) :
    (prepareMeasured seed).1.2+(prepareMeasured seed).2 ≤ 9*(prepareMeasured seed).1.2 := by
  have h := prepareMeasured_emission seed
  omega

theorem prepare_emit_frames (seed : List Bool) :
    BinaryTracePlanMeasured.emitFrames (preparePlan seed).1.2 ≤ 2*(prepare seed).2+1 := by
  have hf := BinaryTracePlanMeasured.emitFrames_bound (preparePlan seed).1.2
  have hp := preparePlan_budget seed
  change _ ≤ 2*(preparePlan seed).2+1
  omega

theorem prepare_plan_references (seed : List Bool) :
    BinaryTracePlanMeasured.planReferences (preparePlan seed).1.2 ≤ 4*(prepare seed).2 := by
  have hr := BinaryTracePlanMeasured.planReferences_bound (preparePlan seed).1.2
  have hp := preparePlan_budget seed
  change _ ≤ 4*(preparePlan seed).2
  omega

theorem prepare_emit_width (seed : List Bool) :
    binaryWordWidth (BinaryTracePlanMeasured.emit (preparePlan seed).1.2 []).2 ≤
      binaryWordWidth (8*(34*seed.length+13)) :=
  binaryWordWidth_mono ((prepare_emit_work seed).trans (Nat.mul_le_mul_left 8 (prepare_bound seed)))

-- The indexed Tree.branch constructor retains its child height at runtime.
-- Generated C computes that height by length of the tail ruler. Count one
-- length-loop terminal plus every visited ruler cell at every branch. This
-- is a proof observer; the selected builder does not execute it separately.
def heightScan : List Bool → ℕ
  | [] => 0
  | _::ruler => ruler.length+1+2*heightScan ruler

theorem heightScan_exact (ruler seed : List Bool) :
    heightScan ruler+ruler.length+1 = BinarySeedLookupTree.buildVisits ruler seed := by
  induction ruler generalizing seed with
  | nil => rfl
  | cons cell ruler ih =>
      have hl := ih seed
      have hr := ih (BinarySeedLookupTree.build ruler seed).2
      simp only [heightScan,BinarySeedLookupTree.buildVisits,List.length_cons]
      omega

theorem buildPlanAt_height_work (ruler seed : List Bool) (depth : ℕ) :
    6*heightScan ruler ≤ (buildPlanAt ruler seed depth).2 := by
  rw [buildPlanAt_work,BinaryWordStoreWork.build_work]
  have h := heightScan_exact ruler seed
  omega

theorem buildAtMeasured_source_emission_height (ruler seed : List Bool) (depth : ℕ) :
    (buildAtMeasured ruler seed depth).1.2+(buildAtMeasured ruler seed depth).2+heightScan ruler ≤
      6*(buildAtMeasured ruler seed depth).1.2 := by
  have he := buildAtMeasured_emission ruler seed depth
  have hh := buildPlanAt_height_work ruler seed depth
  change 6*heightScan ruler ≤ (buildAtMeasured ruler seed depth).1.2 at hh
  omega

theorem prepare_height_work (seed : List Bool) :
    6*heightScan (countAt seed [] 2).1.1 ≤ (prepare seed).2 := by
  have h := buildPlanAt_height_work (countAt seed [] 2).1.1 seed 2
  change _ ≤ (countAt seed [] 2).2+(buildPlanAt (countAt seed [] 2).1.1 seed 2).2+
    (countAt seed [] 2).1.1.length+4
  omega

theorem prepareMeasured_source_emission_height (seed : List Bool) :
    (prepareMeasured seed).1.2+(prepareMeasured seed).2+heightScan (countAt seed [] 2).1.1 ≤
      10*(prepareMeasured seed).1.2 := by
  have he := prepareMeasured_emission seed
  have hh := prepare_height_work seed
  change 6*heightScan (countAt seed [] 2).1.1 ≤ (prepareMeasured seed).1.2 at hh
  omega

end Blotto.BinaryWordStoreMeasured
