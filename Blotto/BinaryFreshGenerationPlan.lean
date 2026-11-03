import Blotto.BooleanFreshSeedAmortized
import Blotto.BinaryTracePlanMeasured

/-! Actual ruler counting and fresh-bit generation build one trace plan at
final depths. Only the complete generator emits it. Source primitive records
and work remain exact; the additional counter is the actual plan-emitter work.
Primitive internals, scalar/reference/layout/allocator/GC prices are separate. -/
namespace Blotto.BinaryFreshGenerationPlan
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage BinaryTraceDepth
open BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 2500000

def countPlanAt {α : Type*} : List α → List Bool → ℕ → (List Bool × Plan) × ℕ
  | [],counter,depth => ((counter,.block [.frames (depth+1),.arrayAllocation 4]),2)
  | _::rest,counter,depth =>
      let advanced := BinaryWordStoreMeasured.carryAt counter (depth+2)
      let later := countPlanAt rest advanced.1.1 (depth+1)
      ((later.1.1,.join (.block [.frames (depth+2),.arrayAllocation 4])
        (.join (.block advanced.1.2) later.1.2)),advanced.2+later.2+1)

theorem countPlanAt_refines {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (((countPlanAt items counter depth).1.1,denote (countPlanAt items counter depth).1.2),
      (countPlanAt items counter depth).2) = BinaryWordStoreMeasured.countAt items counter depth := by
  induction items generalizing counter depth with
  | nil => rfl
  | cons item rest ih =>
      have h := ih (BinaryWordStoreMeasured.carryAt counter (depth+2)).1.1 (depth+1)
      have hd := congrArg (fun p : (List Bool × Trace) × ℕ => p.1.1) h
      have ht := congrArg (fun p : (List Bool × Trace) × ℕ => p.1.2) h
      have hw := congrArg Prod.snd h
      dsimp only at hd ht hw
      simp only [countPlanAt,BinaryWordStoreMeasured.countAt,denote,hd,ht,hw,List.cons_append,List.nil_append]

theorem countPlanAt_data {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countPlanAt items counter depth).1.1 = (BinaryWordStoreMeasured.count items counter).1.1 := by
  have h := congrArg (fun p : (List Bool × Trace) × ℕ => p.1.1) (countPlanAt_refines items counter depth)
  simpa only [BinaryWordStoreMeasured.countAt_data,BinaryWordStoreMeasured.count,
    BinaryWordStoreMeasured.countAt_data] using h

theorem countPlanAt_trace {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    denote (countPlanAt items counter depth).1.2 = under depth (BinaryWordStoreMeasured.count items counter).1.2 := by
  have h := congrArg (fun p : (List Bool × Trace) × ℕ => p.1.2) (countPlanAt_refines items counter depth)
  simpa only [BinaryWordStoreMeasured.countAt_erases,BinaryWordStoreMeasured.count_erases] using h

theorem countPlanAt_work {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    (countPlanAt items counter depth).2 = (BinaryWordStoreMeasured.count items counter).2 := by
  have h := congrArg Prod.snd (countPlanAt_refines items counter depth)
  simpa only [BinaryWordStoreMeasured.countAt_work,BinaryWordStoreMeasured.count_work] using h

theorem countPlanAt_bound {α : Type*} (items : List α) (counter : List Bool) (depth : ℕ) :
    payload (countPlanAt items counter depth).1.2+nodes (countPlanAt items counter depth).1.2 ≤
      6*(countPlanAt items counter depth).2 := by
  induction items generalizing counter depth with
  | nil => simp [countPlanAt,payload,nodes]
  | cons item rest ih =>
      have hl := ih (BinaryWordStoreMeasured.carryAt counter (depth+2)).1.1 (depth+1)
      have hc := BinaryWordStoreMeasured.carryAt_trace_work counter (depth+2)
      simp only [countPlanAt,payload,nodes,List.length_cons,List.length_nil]
      omega

def preparePlanAt {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (depth : ℕ) :
    (List Bool × Plan) × ℕ :=
  let first := countPlanAt request.choiceRuler [] (depth+2)
  let second := countPlanAt request.precisionRuler first.1.1 (depth+2)
  let third := countPlanAt request.precisionRuler second.1.1 (depth+2)
  ((third.1.1,.join (.block [.frames (depth+2),.arrayAllocation 48])
    (.join first.1.2 (.join second.1.2 third.1.2))),first.2+second.2+third.2+8)

theorem preparePlanAt_data {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (depth : ℕ) :
    (preparePlanAt request depth).1.1 = (BinaryPRGRulerSeedMeasured.prepare request).1.1 := by
  simp only [preparePlanAt,BinaryPRGRulerSeedMeasured.prepare,countPlanAt_data]

theorem preparePlanAt_trace {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (depth : ℕ) :
    denote (preparePlanAt request depth).1.2 = under depth (BinaryPRGRulerSeedMeasured.prepare request).1.2 := by
  simp only [preparePlanAt,denote,countPlanAt_trace,countPlanAt_data,BinaryPRGRulerSeedMeasured.prepare,
    wrap,combine,under_append,under_compose,List.append_nil]
  rfl

theorem preparePlanAt_work {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (depth : ℕ) :
    (preparePlanAt request depth).2 = (BinaryPRGRulerSeedMeasured.prepare request).2 := by
  simp only [preparePlanAt,countPlanAt_work,countPlanAt_data,BinaryPRGRulerSeedMeasured.prepare]

theorem preparePlanAt_bound {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) (depth : ℕ) :
    payload (preparePlanAt request depth).1.2+nodes (preparePlanAt request depth).1.2 ≤
      6*(preparePlanAt request depth).2 := by
  have h1 := countPlanAt_bound request.choiceRuler [] (depth+2)
  have h2 := countPlanAt_bound request.precisionRuler (countPlanAt request.choiceRuler [] (depth+2)).1.1 (depth+2)
  have h3 := countPlanAt_bound request.precisionRuler
    (countPlanAt request.precisionRuler (countPlanAt request.choiceRuler [] (depth+2)).1.1 (depth+2)).1.1 (depth+2)
  simp only [preparePlanAt,payload,nodes,List.length_cons,List.length_nil]
  omega

def loopPlanAt {S : Type*} (next : S → Bool × S) (counter reversed : List Bool)
    (state : S) (depth : ℕ) : ((List Bool × S) × Plan) × ℕ :=
  let tested := BooleanFreshSeedMeasured.scanAt counter (depth+2)
  if h : tested.1.1 = true then
    let bit := next state
    let decremented := BooleanFreshSeedMeasured.predecessorAt counter (depth+2)
    let later := loopPlanAt next decremented.1.1 (bit.1::reversed) bit.2 (depth+2)
    ((later.1.1,.join (.block [.listAllocation 1,.frames (depth+2),.arrayAllocation 32])
      (.join (.block tested.1.2) (.join (.block decremented.1.2) later.1.2))),
      tested.2+decremented.2+later.2+8)
  else
    let result := BinarySeedCursorMeasured.reverseAt reversed [] (depth+2)
    (((result.1.1,state),.join (.block [.frames (depth+2),.arrayAllocation 24])
      (.join (.block tested.1.2) (.block result.1.2))),tested.2+result.2+4)
termination_by BinaryBigEndian.littleValue counter
decreasing_by
  have hp : 0 < BinaryBigEndian.littleValue counter := by
    apply (BinaryEuclideanGCD.nonzero_true_iff counter).mp
    change (BooleanFreshSeedMeasured.scanAt counter (depth+2)).1.1 = true at h
    simpa only [BooleanFreshSeedMeasured.scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using h
  rw [BooleanFreshSeedMeasured.predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
  have hd := BinaryStoredCountdown.predecessor_value counter hp
  omega

theorem loopPlanAt_refines {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (((loopPlanAt next counter reversed state depth).1.1,denote (loopPlanAt next counter reversed state depth).1.2),
      (loopPlanAt next counter reversed state depth).2) = BooleanFreshSeedMeasured.loopAt next counter reversed state depth := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      (((loopPlanAt next counter reversed state depth).1.1,denote (loopPlanAt next counter reversed state depth).1.2),
        (loopPlanAt next counter reversed state depth).2) = BooleanFreshSeedMeasured.loopAt next counter reversed state depth := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        rw [loopPlanAt,BooleanFreshSeedMeasured.loopAt]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BooleanFreshSeedMeasured.scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hData : (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 =
              BinaryStoredCountdown.predecessor counter := by
            rw [BooleanFreshSeedMeasured.predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          have hLess : BinaryBigEndian.littleValue (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 < count := by
            rw [hData]; omega
          have hi := ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)
          have hiData := congrArg (fun p : ((List Bool × S) × Trace) × ℕ => p.1.1) hi
          have hiTrace := congrArg (fun p : ((List Bool × S) × Trace) × ℕ => p.1.2) hi
          have hiWork := congrArg Prod.snd hi
          dsimp only at hiData hiTrace hiWork
          simp only [denote,hiData,hiTrace,hiWork,List.cons_append,List.nil_append]
        · simp only [denote,List.cons_append,List.nil_append]
  exact hAll _ counter rfl reversed state depth

theorem loopPlanAt_data {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopPlanAt next counter reversed state depth).1.1 =
      (BooleanFreshSeedMeasured.loop next counter reversed state).1.1 := by
  have h := congrArg (fun p : ((List Bool × S) × Trace) × ℕ => p.1.1)
    (loopPlanAt_refines next counter reversed state depth)
  simpa only [BooleanFreshSeedMeasured.loopAt_erases,BooleanFreshSeedMeasured.loop_erases] using h

theorem loopPlanAt_trace {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    denote (loopPlanAt next counter reversed state depth).1.2 =
      under depth (BooleanFreshSeedMeasured.loop next counter reversed state).1.2 := by
  have h := congrArg (fun p : ((List Bool × S) × Trace) × ℕ => p.1.2)
    (loopPlanAt_refines next counter reversed state depth)
  simpa only [BooleanFreshSeedMeasured.loopAt_erases,BooleanFreshSeedMeasured.loop_erases] using h

theorem loopPlanAt_work {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopPlanAt next counter reversed state depth).2 =
      (BooleanFreshSeedMeasured.loop next counter reversed state).2 := by
  have h := congrArg Prod.snd (loopPlanAt_refines next counter reversed state depth)
  exact h.trans (BooleanFreshSeedAmortized.loopAt_work_eq next counter reversed state depth)

theorem loopPlanAt_bound {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    payload (loopPlanAt next counter reversed state depth).1.2+nodes (loopPlanAt next counter reversed state depth).1.2 ≤
      6*(loopPlanAt next counter reversed state depth).2 := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      payload (loopPlanAt next counter reversed state depth).1.2+nodes (loopPlanAt next counter reversed state depth).1.2 ≤
        6*(loopPlanAt next counter reversed state depth).2 := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        rw [loopPlanAt]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BooleanFreshSeedMeasured.scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hData : (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 =
              BinaryStoredCountdown.predecessor counter := by
            rw [BooleanFreshSeedMeasured.predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          have hLess : BinaryBigEndian.littleValue (BooleanFreshSeedMeasured.predecessorAt counter (depth+2)).1.1 < count := by
            rw [hData]; omega
          have hi := ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)
          have hs := BinarySeedTraceBounds.scan_trace_work counter (depth+2)
          have hp := BinarySeedTraceBounds.predecessor_trace_work counter (depth+2)
          simp only [payload,nodes,List.length_cons,List.length_nil]
          omega
        · have hs := BinarySeedTraceBounds.scan_trace_work counter (depth+2)
          have hr := BinarySeedTraceBounds.reverse_trace_work reversed [] (depth+2)
          simp only [payload,nodes,List.length_cons,List.length_nil]
          omega
  exact hAll _ counter rfl reversed state depth

def generatePlan {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) : ((List Bool × S) × Plan) × ℕ :=
  let counter := preparePlanAt request 2
  let seed := loopPlanAt next counter.1.1 [] state 2
  ((seed.1.1,.join (.block [.frames 2,.arrayAllocation 32]) (.join counter.1.2 seed.1.2)),counter.2+seed.2+4)

theorem generatePlan_data {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generatePlan next request state).1.1 = (BinaryPRGRulerSeedMeasured.generate next request state).1.1 := by
  simp only [generatePlan,preparePlanAt_data,loopPlanAt_data,BinaryPRGRulerSeedMeasured.generate,
    BooleanFreshSeedMeasured.generate]

theorem generatePlan_trace {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    denote (generatePlan next request state).1.2 = (BinaryPRGRulerSeedMeasured.generate next request state).1.2 := by
  simp only [generatePlan,denote,preparePlanAt_trace,preparePlanAt_data,loopPlanAt_trace,
    BinaryPRGRulerSeedMeasured.generate,BooleanFreshSeedMeasured.generate,wrap,combine,List.append_nil]

theorem generatePlan_work {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generatePlan next request state).2 = (BinaryPRGRulerSeedMeasured.generate next request state).2 := by
  simp only [generatePlan,preparePlanAt_work,preparePlanAt_data,loopPlanAt_work,
    BinaryPRGRulerSeedMeasured.generate,BooleanFreshSeedMeasured.generate]

theorem generatePlan_bound {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    payload (generatePlan next request state).1.2+nodes (generatePlan next request state).1.2 ≤
      6*(generatePlan next request state).2 := by
  have hc := preparePlanAt_bound request 2
  have hs := loopPlanAt_bound next (preparePlanAt request 2).1.1 [] state 2
  simp only [generatePlan,payload,nodes,List.length_cons,List.length_nil]
  omega

def generateWithEmission {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (((List Bool × S) × Trace) × ℕ) × ℕ :=
  let planned := generatePlan next request state
  let emitted := emit planned.1.2 []
  (((planned.1.1,emitted.1),planned.2),emitted.2)

theorem generateWithEmission_compat {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generateWithEmission next request state).1 = BinaryPRGRulerSeedMeasured.generate next request state := by
  simp only [generateWithEmission,emit_data,List.append_nil,generatePlan_data,generatePlan_trace,generatePlan_work]

theorem generateWithEmission_bound {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generateWithEmission next request state).2 ≤ 24*(BinaryPRGRulerSeedMeasured.generate next request state).2 := by
  have h := emit_work_bound (generatePlan next request state).1.2 []
    (6*(generatePlan next request state).2) (generatePlan_bound next request state)
  simp only [generateWithEmission,generatePlan_work] at h ⊢
  omega

theorem generateWithEmission_exact {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generateWithEmission next request state).2 =
      4*payload (generatePlan next request state).1.2+2*nodes (generatePlan next request state).1.2 := by
  exact emit_work (generatePlan next request state).1.2 []

theorem physical_emission_linear {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : BinaryTerminalPhysicalAllowanceCache.Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    (generateWithEmission next parsed.1.2.logical state).2 ≤ 9600000*(frame.length+1) := by
  have he := generateWithEmission_bound next parsed.1.2.logical state
  have hw := BooleanFreshSeedAmortized.physical_generation_linear next frame parsed hRead state
  omega

theorem generatePlan_references {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    planReferences (generatePlan next request state).1.2 ≤ 12*(BinaryPRGRulerSeedMeasured.generate next request state).2 := by
  have hr := planReferences_bound (generatePlan next request state).1.2
  have hb := generatePlan_bound next request state
  rw [generatePlan_work] at hb
  omega

theorem generatePlan_emitter_frames {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    emitFrames (generatePlan next request state).1.2 ≤ 6*(BinaryPRGRulerSeedMeasured.generate next request state).2+1 := by
  have hf := emitFrames_bound (generatePlan next request state).1.2
  have hb := generatePlan_bound next request state
  rw [generatePlan_work] at hb
  omega

theorem physical_plan_components {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : BinaryTerminalPhysicalAllowanceCache.Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    let planned := generatePlan next parsed.1.2.logical state
    payload planned.1.2+nodes planned.1.2 ≤ 2400000*(frame.length+1) ∧
      planReferences planned.1.2 ≤ 4800000*(frame.length+1) ∧
      emitFrames planned.1.2 ≤ 2400000*(frame.length+1)+1 := by
  have hb := generatePlan_bound next parsed.1.2.logical state
  rw [generatePlan_work] at hb
  have hr := generatePlan_references next parsed.1.2.logical state
  have hf := generatePlan_emitter_frames next parsed.1.2.logical state
  have hw := BooleanFreshSeedAmortized.physical_generation_linear next frame parsed hRead state
  dsimp only
  omega

end Blotto.BinaryFreshGenerationPlan
