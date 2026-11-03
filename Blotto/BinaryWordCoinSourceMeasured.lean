import Blotto.BinaryWordCoinMeasured
import Blotto.BinaryHeapEnumerationMeasured
import Blotto.BinaryCoinTestsMeasured
import Blotto.BinaryTracePlanMeasured

/-! The actual measured coin carries the original controller source charge
on its reached path, together with actual reached guard/step primitive work.
No second complete coin runs to recover either charge.
The body reservation uses actual test counters and cached word widths. Test
traces use the linear returned-ruler emitter. Whole coin recursion retains
absolute-depth plans and emits once at the requested outer entry. A separate
returned charge prices emission list/control and reached shift primitives;
old result/source/guard-step records remain exact. Native scalar arithmetic
and other metadata/reference/allocator costs remain separate. -/
namespace Blotto.BinaryWordCoinSourceMeasured
open BinarySeedPreparationSpace BinarySeedLookupTree BinaryRationalNormalization BinaryPRGHeapTraceUsage
open BinaryWordCoinPrimitivesMeasured
open BinaryTraceDepth
open BinaryTracePlanMeasured (Plan)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def runMeasuredReference {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) :
    (((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let zeroScan := BinaryCoinTestsMeasured.zero a.bits
  let sameScan := BinaryCoinTestsMeasured.same a.bits b.bits
  let body := BinaryCoinTestsMeasured.charge w zeroScan sameScan
  let tested := BinaryCoinTestsMeasured.emit zeroScan
  let first := [.frames 2,.arrayAllocation 16]++under 2 tested.2
  if tested.1 then ((((some false,pc),first),body),0) else
    let compared := BinaryCoinTestsMeasured.emit sameScan
    let second := first++under 2 compared.2
    if compared.1 then ((((some true,pc),second),body),0) else
      let guarded := ltMeasured pc store.cap
      let third := second++under 2 guarded.1.1.2
      if hRead : guarded.1.1.1 = true then
        let read := lookup store pc
        let next := stepMeasured a b
        let advanced := increment pc
        let localTrace := third++under 2 read.1.2++under 2 next.1.1.2++under 2 advanced.1.2
        let work := body+(10*(store.width+1)+2*store.width)+(2*store.width+1)+(advanced.2-2)
        if read.1.1 = next.1.1.1.1 then
          let later := runMeasuredReference store next.1.1.1.2 b advanced.1.1.1 (BinaryWordCoinMeasured.advance_bound store pc hRead)
          (((later.1.1.1,localTrace++under 1 later.1.1.2),work+later.1.2),guarded.2+next.2+later.2)
        else ((((some (!read.1.1),advanced.1.1.1),localTrace),work),guarded.2+next.2)
      else ((((none,pc),third),body+(10*(store.width+1)+2*store.width)),guarded.2)
termination_by store.cap.value-pc.value
decreasing_by
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [guarded,ltMeasured_compat,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead)
  omega


-- These two transformations are proof companions, never selected producers.
def projected {α : Type} (result : ((α × Plan) × ℕ) × ℕ) : ((α × Trace) × ℕ) × ℕ :=
  (((result.1.1.1,BinaryTracePlanMeasured.denote result.1.1.2),result.1.2),result.2)

def offset {α : Type} (depth : ℕ) (result : ((α × Trace) × ℕ) × ℕ) : ((α × Trace) × ℕ) × ℕ :=
  (((result.1.1.1,under depth result.1.1.2),result.1.2),result.2)

def runPlanAt {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (_hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (((Option Bool × FixedBinaryWord store.width) × Plan) × ℕ) × ℕ :=
  let zeroScan := BinaryCoinTestsMeasured.zero a.bits
  let sameScan := BinaryCoinTestsMeasured.same a.bits b.bits
  let body := BinaryCoinTestsMeasured.charge w zeroScan sameScan
  let tested := BinaryCoinTestsMeasured.emit zeroScan
  let first := Plan.join (.block [.frames (depth+2),.arrayAllocation 16]) (.shifted (depth+2) tested.2)
  if tested.1 then ((((some false,pc),first),body),0) else
    let compared := BinaryCoinTestsMeasured.emit sameScan
    let second := Plan.join first (.shifted (depth+2) compared.2)
    if compared.1 then ((((some true,pc),second),body),0) else
      let guarded := ltMeasured pc store.cap
      let third := Plan.join second (.shifted (depth+2) guarded.1.1.2)
      if hRead : guarded.1.1.1 = true then
        let read := lookup store pc
        let next := stepMeasured a b
        let advanced := increment pc
        let localPlan := Plan.join third (.join (.shifted (depth+2) read.1.2)
          (.join (.shifted (depth+2) next.1.1.2) (.shifted (depth+2) advanced.1.2)))
        let work := body+(10*(store.width+1)+2*store.width)+(2*store.width+1)+(advanced.2-2)
        if read.1.1 = next.1.1.1.1 then
          let later := runPlanAt store next.1.1.1.2 b advanced.1.1.1
            (BinaryWordCoinMeasured.advance_bound store pc hRead) (depth+1)
          (((later.1.1.1,.join localPlan later.1.1.2),work+later.1.2),guarded.2+next.2+later.2)
        else ((((some (!read.1.1),advanced.1.1.1),localPlan),work),guarded.2+next.2)
      else ((((none,pc),third),body+(10*(store.width+1)+2*store.width)),guarded.2)
termination_by store.cap.value-pc.value
decreasing_by
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [guarded,ltMeasured_compat,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead)
  omega

theorem runPlanAt_refines {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    projected (runPlanAt store a b pc hp depth) = offset depth (runMeasuredReference store a b pc hp) := by
  conv_lhs => unfold projected runPlanAt
  conv_rhs => unfold offset runMeasuredReference
  dsimp only
  simp only [BinaryTracePlanMeasured.denote,under_append,BinaryTraceDepth.under_compose,List.append_assoc]
  split_ifs with hz he hRead hd
  all_goals simp only [BinaryTracePlanMeasured.denote,under_append,BinaryTraceDepth.under_compose,List.append_assoc]
  all_goals first
    | rfl
    | have hpNext := BinaryWordCoinMeasured.advance_bound store pc hRead
      have hLater := runPlanAt_refines store (stepMeasured a b).1.1.1.2 b (increment pc).1.1.1 hpNext (depth+1)
      have hData := congrArg (fun output => output.1.1.1) hLater
      have hTrace := congrArg (fun output => output.1.1.2) hLater
      have hWork := congrArg (fun output => output.1.2) hLater
      have hExtra := congrArg Prod.snd hLater
      dsimp only [projected,offset] at hData hTrace hWork hExtra
      simp only [hData,hTrace,hWork,hExtra,BinaryTracePlanMeasured.denote,under_append,BinaryTraceDepth.under_compose,List.append_assoc]
      rfl
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (ltMeasured pc store.cap).1.1.1 = true := by assumption
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [ltMeasured_compat,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead'
  omega


theorem runPlanAt_data {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runPlanAt store a b pc hp depth).1.1.1 = (runMeasuredReference store a b pc hp).1.1.1 := by
  have h := congrArg (fun output => output.1.1.1) (runPlanAt_refines store a b pc hp depth)
  exact h


theorem runPlanAt_trace {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.denote (runPlanAt store a b pc hp depth).1.1.2 = under depth (runMeasuredReference store a b pc hp).1.1.2 := by
  have h := congrArg (fun output => output.1.1.2) (runPlanAt_refines store a b pc hp depth)
  exact h


theorem runPlanAt_work {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runPlanAt store a b pc hp depth).1.2 = (runMeasuredReference store a b pc hp).1.2 := by
  have h := congrArg (fun output => output.1.2) (runPlanAt_refines store a b pc hp depth)
  exact h


theorem runPlanAt_extra {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runPlanAt store a b pc hp depth).2 = (runMeasuredReference store a b pc hp).2 := by
  have h := congrArg (fun output => output.2) (runPlanAt_refines store a b pc hp depth)
  exact h

def runTraceMeasured {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    ((((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ) × ℕ :=
  let planned := runPlanAt store a b pc hp depth
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.2 []
  ((((planned.1.1.1,emitted.1.1),planned.1.2),planned.2),emitted.1.2+emitted.2)

def runMeasured {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ := (runTraceMeasured store a b pc hp 0).1

theorem runMeasured_eq_reference {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    runMeasured store a b pc hp = runMeasuredReference store a b pc hp := by
  have h := runPlanAt_refines store a b pc hp 0
  simpa only [runMeasured,runTraceMeasured,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,projected,offset,BinaryTraceDepth.under_zero] using h

def run {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ := (runMeasured store a b pc hp).1

theorem runMeasured_compat {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runMeasured store a b pc hp).1 = run store a b pc hp := rfl


theorem runMeasuredReference_compat {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runMeasuredReference store a b pc hp).1 = run store a b pc hp := by
  rw [run,runMeasured_eq_reference]

theorem run_erases {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).1 = BinaryWordCoinLifetime.runWithTrace store a b pc hp := by
  conv_lhs => unfold run; rw [runMeasured_eq_reference]; unfold runMeasuredReference
  conv_rhs => unfold BinaryWordCoinLifetime.runWithTrace
  dsimp only
  simp only [BinaryCoinTestsMeasured.zero_compat,BinaryCoinTestsMeasured.same_compat,
    runMeasuredReference_compat,ltMeasured_compat,stepMeasured_compat,
    zero_erases,same_erases,lt_erases,lookup_erases,step_erases,increment_erases,
    BinaryWordCoinLifetime.earlyTrace,BinaryWordCoinLifetime.equalTrace,
    BinaryWordCoinLifetime.guardTrace,BinaryWordCoinLifetime.readTrace]
  split_ifs with hz he hRead hd
  all_goals first
    | rfl
    | have hpNext : (BinaryWordStoreLifetime.incrementWithTrace pc).1.1.value ≤ store.cap.value := by
        rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
        exact BinaryWordIndexCoinController.advance_bound store pc
          (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead)
      have hLater := run_erases store (BinaryWordCoinLifetime.stepWithTrace a b).1.2 b
        (BinaryWordStoreLifetime.incrementWithTrace pc).1.1 hpNext
      exact congrArg (fun output : (Option Bool × FixedBinaryWord store.width) × Trace =>
        (output.1,BinaryWordCoinLifetime.readTrace store a b pc++under 1 output.2)) hLater
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (BinaryWordStoreLifetime.ltWithTrace pc store.cap).1 = true := by assumption
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  have hn := BinaryWordIndexCoinController.advance_value store pc
    (by simpa only [BinaryWordStoreLifetime.ltWithTrace_erases,BinaryIndexWord.ltWithWork] using hRead')
  change (BinaryIndexWord.increment pc).1.value = pc.value+1 at hn
  rw [BinaryWordStoreLifetime.incrementWithTrace_erases]
  omega

theorem highVisits_eq (bits : List Bool) : BinaryWordHighBit.visits bits = max 1 bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases rest with
    | nil => rfl
    | cons next tail => simp only [BinaryWordHighBit.visits,List.length_cons] at ih ⊢; omega

theorem stepWork_eq (a b : List Bool) (h : a.length = b.length) :
    BinaryCoinWord.stepWork a b = 17*a.length+18 := by
  have hs := BinaryBorrowWord.visits_eq (false::a) (b++[false]) (BinaryCoinWord.input_lengths a b h)
  simp only [BinaryCoinWord.stepWork,highVisits_eq,BinaryCoinWord.chosenResidual_length a b h,
    hs,List.length_cons]
  omega

theorem body_eq {w : ℕ} (a b : FixedBinaryWord w) :
    3*FixedBinaryWord.zeroVisits a.bits+4*FixedBinaryWord.sameVisits a.bits b.bits+17*a.bits.length+22 =
      FixedWordCoin.bodyWork a b+2 := by
  rw [FixedWordCoin.bodyWork,stepWork_eq a.bits b.bits (a.size.trans b.size.symm)]
  omega

theorem guard_work (store : Store) (pc : FixedBinaryWord store.width) :
    (BinaryIndexWord.ltWithWork pc store.cap).2 = 10*(pc.bits.length+1)+2*pc.bits.length := by
  simp only [BinaryIndexWord.ltWithWork,
    BinaryBorrowWord.visits_eq pc.bits store.cap.bits (pc.size.trans store.cap.size.symm)]

theorem increment_work {w : ℕ} (pc : FixedBinaryWord w) :
    (increment pc).2-2 = (BinaryIndexWord.incrementWithWork pc).2 := by
  simp only [increment,incrementAt_work,BinaryIndexWord.incrementWithWork,pc.size]
  omega

theorem lookup_source_work (store : Store) (pc : FixedBinaryWord store.width) :
    (store.lookupWithVisits pc).2 = 2*pc.bits.length+1 := by
  change store.lookupVisits pc = _
  rw [store.lookupVisits_exact pc,pc.size]

theorem run_work {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (run store a b pc hp).2 = (BinaryWordIndexCoinController.run store a b pc hp).2 := by
  conv_lhs => unfold run; rw [runMeasured_eq_reference]; unfold runMeasuredReference
  conv_rhs => unfold BinaryWordIndexCoinController.run
  dsimp only
  simp only [BinaryCoinTestsMeasured.zero_compat,BinaryCoinTestsMeasured.same_compat,BinaryCoinTestsMeasured.charge_eq,
    runMeasuredReference_compat,ltMeasured_compat,stepMeasured_compat,
    body_eq,zero_erases,same_erases,lt_erases,lookup_erases,step_erases,increment_work,
    BinaryWordCoinLifetime.zeroWithTrace_erases,BinaryWordCoinLifetime.sameWithTrace_erases,
    BinaryWordStoreLifetime.ltWithTrace_erases,BinaryWordStoreLifetime.lookupWithTrace_erases,
    BinaryWordCoinLifetime.stepWithTrace_erases,increment_erases,BinaryWordStoreLifetime.incrementWithTrace_erases,
    FixedBinaryWord.isZero,FixedBinaryWord.same,guard_work,BinaryIndexWord.ltWithWork_state,
    BinaryIndexWord.incrementWithWork_state,BinarySeedLookupTree.Store.lookupWithVisits_state,
    lookup_source_work,pc.size]
  split_ifs with hz he hRead hd <;> simp_all only []
  all_goals first
    | rfl
    | rw [run_work]
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : BinaryIndexWord.lt pc store.cap = true := by assumption
  have hr := (BinaryIndexWord.lt_value pc store.cap).mp hRead'
  have hn := BinaryWordIndexCoinController.advance_value store pc hRead'
  change (BinaryIndexWord.increment pc).1.value = pc.value+1 at hn
  omega

def sampleMeasuredReference (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  let W := width word
  let a := pad W word.numerator
  let b := pad W word.denominator
  have ha : a.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  let later := runMeasuredReference store ⟨a.1.1,ha⟩ ⟨b.1.1,hb⟩ pc hp
  (((later.1.1.1,[.frames (W+8),.arrayAllocation 16]++under 2 a.1.2++under 2 b.1.2++under 2 later.1.1.2),
    12*(W+1)+later.1.2),later.2)

def samplePlanAt (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) : (((Option Bool × FixedBinaryWord store.width) × Plan) × ℕ) × ℕ :=
  let W := width word
  let a := pad W word.numerator
  let b := pad W word.denominator
  have ha : a.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  let later := runPlanAt store ⟨a.1.1,ha⟩ ⟨b.1.1,hb⟩ pc hp (depth+2)
  (((later.1.1.1,.join (.block [.frames (depth+(W+8)),.arrayAllocation 16])
      (.join (.shifted (depth+2) a.1.2) (.join (.shifted (depth+2) b.1.2) later.1.1.2))),
    12*(W+1)+later.1.2),later.2)


theorem samplePlanAt_refines (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    projected (samplePlanAt store word pc hp depth) = offset depth (sampleMeasuredReference store word pc hp) := by
  simp only [projected,offset,samplePlanAt,sampleMeasuredReference,BinaryTracePlanMeasured.denote,
    runPlanAt_data,runPlanAt_trace,runPlanAt_work,runPlanAt_extra,under_append,
    BinaryTraceDepth.under_compose,List.append_assoc]
  rfl

def sampleTraceMeasured (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    ((((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ) × ℕ :=
  let planned := samplePlanAt store word pc hp depth
  let emitted := BinaryTracePlanMeasured.emitFull planned.1.1.2 []
  ((((planned.1.1.1,emitted.1.1),planned.1.2),planned.2),emitted.1.2+emitted.2)

def sampleMeasured (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ) × ℕ :=
  (sampleTraceMeasured store word pc hp 0).1

theorem sampleMeasured_eq_reference (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : sampleMeasured store word pc hp = sampleMeasuredReference store word pc hp := by
  have h := samplePlanAt_refines store word pc hp 0
  simpa only [sampleMeasured,sampleTraceMeasured,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,projected,offset,BinaryTraceDepth.under_zero] using h

def sample (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : ((Option Bool × FixedBinaryWord store.width) × Trace) × ℕ :=
  (sampleMeasured store word pc hp).1

theorem sampleMeasured_compat (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) : (sampleMeasured store word pc hp).1 = sample store word pc hp := rfl

theorem sample_erases (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (sample store word pc hp).1 = BinaryWordCoinLifetime.sampleWithTrace store word pc hp := by
  simp only [sample,sampleMeasured_eq_reference,sampleMeasuredReference,runMeasuredReference_compat,BinaryWordCoinLifetime.sampleWithTrace,run_erases,pad_erases]

theorem sample_data (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (sample store word pc hp).1.1 = (BinaryWordIndexCoinController.sample store word pc hp).1 := by
  rw [sample_erases]
  exact (BinaryWordCoinLifetime.sampleWithTrace_erases store word pc hp).trans
    (BinaryPRGWordControllerDataCoin.sample_erasure store word pc hp).symm

theorem sample_work (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (sample store word pc hp).2 = (BinaryWordIndexCoinController.sample store word pc hp).2 := by
  simp only [sample,sampleMeasured_eq_reference,sampleMeasuredReference,runMeasuredReference_compat,BinaryWordIndexCoinController.sample,run_work,
    pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
  rfl

theorem sample_position (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (sample store word pc hp).1.1.2.value ∧
      (sample store word pc hp).1.1.2.value ≤ store.cap.value := by
  rw [sample_erases]
  exact BinaryWordCoinLifetime.sampleWithTrace_position store word pc hp

theorem zeroVisits_pos (bits : List Bool) : 1 ≤ FixedBinaryWord.zeroVisits bits := by
  cases bits with
  | nil => rfl
  | cons bit rest => cases bit <;> simp [FixedBinaryWord.zeroVisits]

theorem guard_primitive_work_bound (store : Store) (pc : FixedBinaryWord store.width) :
    (ltMeasured pc store.cap).2 ≤ 4*(10*(pc.bits.length+1)+2*pc.bits.length) := by
  have h := ltMeasured_work_bound pc store.cap
  change (ltMeasured pc store.cap).2 ≤ 2*(16*(store.width+1)) at h
  have hSize := pc.size
  omega

theorem step_primitive_work_bound {w : ℕ} (a b : FixedBinaryWord w) :
    (stepMeasured a b).2 ≤ 4*(3*FixedBinaryWord.zeroVisits a.bits+
      4*FixedBinaryWord.sameVisits a.bits b.bits+17*a.bits.length+22) := by
  have h := stepMeasured_work_bound a b
  have hs := step_work a b
  have hz := zeroVisits_pos a.bits
  rw [a.size]
  omega

def Covered {α : Type} (result : (α × ℕ) × ℕ) : Prop := result.2 ≤ 4*result.1.2

theorem runMeasured_covered {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    Covered (runMeasured store a b pc hp) := by
  have hg := guard_primitive_work_bound store pc
  have hs := step_primitive_work_bound a b
  have haSize := a.size
  have hpSize := pc.size
  rw [runMeasured_eq_reference]
  unfold runMeasuredReference
  dsimp only
  simp only [BinaryCoinTestsMeasured.charge_eq]
  split_ifs with hz he hRead hd
  all_goals first
    | (unfold Covered; dsimp only; omega)
    | have hpNext := BinaryWordCoinMeasured.advance_bound store pc hRead
      have hLater := runMeasured_covered store (stepMeasured a b).1.1.1.2 b
        (increment pc).1.1.1 hpNext
      rw [runMeasured_eq_reference] at hLater
      unfold Covered at hLater ⊢
      dsimp only at hLater ⊢
      omega
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (ltMeasured pc store.cap).1.1.1 = true := by assumption
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [ltMeasured_compat,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead'
  omega

theorem runMeasured_work_bound {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    (runMeasured store a b pc hp).2 ≤ 4*(run store a b pc hp).2 :=
  runMeasured_covered store a b pc hp

theorem sampleMeasured_work_bound (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) :
    (sampleMeasured store word pc hp).2 ≤ 4*(sample store word pc hp).2 := by
  let W := width word
  let a := pad W word.numerator
  let b := pad W word.denominator
  have ha : a.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  have h := runMeasured_work_bound store ⟨a.1.1,ha⟩ ⟨b.1.1,hb⟩ pc hp
  simp only [run,runMeasured_eq_reference] at h
  simp only [sample,sampleMeasured_eq_reference,sampleMeasuredReference]
  dsimp only [a,b,W] at h
  omega

theorem zero_trace_length (bits : List Bool) :
    (BinaryCoinTestsMeasured.emit (BinaryCoinTestsMeasured.zero bits)).2.length =
      2*FixedBinaryWord.zeroVisits bits := by
  simp only [BinaryCoinTestsMeasured.emit,BinaryCoinTestsMeasured.events_length,
    BinaryCoinTestsMeasured.zero_ruler,BinaryCoinTestsMeasured.zero_visits]

theorem same_trace_length (first second : List Bool) :
    (BinaryCoinTestsMeasured.emit (BinaryCoinTestsMeasured.same first second)).2.length =
      2*FixedBinaryWord.sameVisits first second := by
  simp only [BinaryCoinTestsMeasured.emit,BinaryCoinTestsMeasured.events_length,
    BinaryCoinTestsMeasured.same_ruler,BinaryCoinTestsMeasured.same_visits]

theorem guard_trace_length {w : ℕ} (first second : FixedBinaryWord w) :
    (ltMeasured first second).1.1.2.length = 3 := rfl

theorem step_trace_length {w : ℕ} (a b : FixedBinaryWord w) :
    (stepMeasured a b).1.1.2.length = 3 := rfl

theorem increment_trace_length {w : ℕ} (pc : FixedBinaryWord w) :
    (increment pc).1.2.length ≤ 3*(w+1)+2 :=
  incrementAt_trace_length pc 0

theorem scanTree_trace_length {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    (scanTree tree address).1.2.length = 2*(depth+1) :=
  scanTreeAt_trace_length tree address 0

theorem lookup_trace_length (store : Store) (pc : FixedBinaryWord store.width) :
    (lookup store pc).1.2.length = 4*store.width+5 :=
  lookupAt_trace_length store pc 0

theorem replicate_trace_length (n : ℕ) (bit : Bool) :
    (replicate n bit).1.2.length = 2*n+1 :=
  replicateAt_trace_length n bit 0

theorem append_trace_length (left right : List Bool) :
    (BinaryWordCoinPrimitivesMeasured.append left right).1.2.length = 2*left.length+1 :=
  appendAt_trace_length left right 0

theorem pad_trace_length (W : ℕ) (bits : List Bool) (h : bits.length ≤ W) :
    (pad W bits).1.2.length = 2*W+4 :=
  padAt_trace_length W bits 0 h

theorem runPlanAt_budget {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.payload (runPlanAt store a b pc hp depth).1.1.2+
      BinaryTracePlanMeasured.nodes (runPlanAt store a b pc hp depth).1.1.2 ≤
        2*(runPlanAt store a b pc hp depth).1.2 := by
  have hl := lookup_trace_length store pc
  have hi := increment_trace_length pc
  conv_lhs => unfold runPlanAt
  conv_rhs => unfold runPlanAt
  dsimp only
  simp only [BinaryCoinTestsMeasured.charge_eq]
  split_ifs with hz he hRead hd
  all_goals simp only [BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
    List.length_cons,List.length_nil,zero_trace_length,same_trace_length,
    guard_trace_length,step_trace_length]
  all_goals first
    | omega
    | have hpNext := BinaryWordCoinMeasured.advance_bound store pc hRead
      have hLater := runPlanAt_budget store (stepMeasured a b).1.1.1.2 b
        (increment pc).1.1.1 hpNext (depth+1)
      omega
termination_by store.cap.value-pc.value
decreasing_by
  have hRead' : (ltMeasured pc store.cap).1.1.1 = true := by assumption
  have hr : pc.value < store.cap.value := (BinaryIndexWord.lt_value pc store.cap).mp
    (by simpa only [ltMeasured_compat,lt_erases,BinaryWordStoreLifetime.ltWithTrace_erases] using hRead')
  have hn := BinaryWordCoinMeasured.advance_value store pc hRead'
  omega

theorem samplePlanAt_budget (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.payload (samplePlanAt store word pc hp depth).1.1.2+
      BinaryTracePlanMeasured.nodes (samplePlanAt store word pc hp depth).1.1.2 ≤
        2*(samplePlanAt store word pc hp depth).1.2 := by
  let W := width word
  let a := pad W word.numerator
  let b := pad W word.denominator
  have ha : a.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_left _ _)
  have hb : b.1.1.length = W := by
    rw [pad_erases,BinaryWordCoinLifetime.padWithTrace_erases]
    exact BinarySignedMagnitude.pad_length W _ (Nat.le_max_right _ _)
  have hLater := runPlanAt_budget store ⟨a.1.1,ha⟩ ⟨b.1.1,hb⟩ pc hp (depth+2)
  have hA := pad_trace_length W word.numerator (Nat.le_max_left _ _)
  have hB := pad_trace_length W word.denominator (Nat.le_max_right _ _)
  simp only [samplePlanAt,BinaryTracePlanMeasured.payload,BinaryTracePlanMeasured.nodes,
    List.length_cons,List.length_nil]
  dsimp only [W,a,b] at hLater hA hB
  omega

theorem runTraceMeasured_refines {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runTraceMeasured store a b pc hp depth).1 = offset depth (runMeasuredReference store a b pc hp) := by
  simpa only [runTraceMeasured,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,projected] using
      runPlanAt_refines store a b pc hp depth

theorem sampleTraceMeasured_refines (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (sampleTraceMeasured store word pc hp depth).1 = offset depth (sampleMeasuredReference store word pc hp) := by
  simpa only [sampleTraceMeasured,BinaryTracePlanMeasured.emitFull_erases,
    BinaryTracePlanMeasured.emit_data,List.append_nil,projected] using
      samplePlanAt_refines store word pc hp depth

theorem runTraceMeasured_emission {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runTraceMeasured store a b pc hp depth).2 ≤ 10*(runTraceMeasured store a b pc hp depth).1.1.2 := by
  have h := BinaryTracePlanMeasured.emitFull_total (runPlanAt store a b pc hp depth).1.1.2 []
    (2*(runPlanAt store a b pc hp depth).1.2) (runPlanAt_budget store a b pc hp depth)
  dsimp only [runTraceMeasured]
  omega

theorem sampleTraceMeasured_emission (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (sampleTraceMeasured store word pc hp depth).2 ≤ 10*(sampleTraceMeasured store word pc hp depth).1.1.2 := by
  have h := BinaryTracePlanMeasured.emitFull_total (samplePlanAt store word pc hp depth).1.1.2 []
    (2*(samplePlanAt store word pc hp depth).1.2) (samplePlanAt_budget store word pc hp depth)
  dsimp only [sampleTraceMeasured]
  omega

theorem runTraceMeasured_primitive {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runTraceMeasured store a b pc hp depth).1.2 ≤ 4*(runTraceMeasured store a b pc hp depth).1.1.2 := by
  have h := runMeasured_covered store a b pc hp
  rw [runMeasured_eq_reference] at h
  rw [runTraceMeasured_refines]
  exact h

theorem sampleTraceMeasured_primitive (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (sampleTraceMeasured store word pc hp depth).1.2 ≤ 4*(sampleTraceMeasured store word pc hp depth).1.1.2 := by
  have h := sampleMeasured_work_bound store word pc hp
  simp only [sample,sampleMeasured_eq_reference] at h
  rw [sampleTraceMeasured_refines]
  exact h

theorem runTraceMeasured_total {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (runTraceMeasured store a b pc hp depth).1.1.2+(runTraceMeasured store a b pc hp depth).1.2+
      (runTraceMeasured store a b pc hp depth).2 ≤ 15*(runTraceMeasured store a b pc hp depth).1.1.2 := by
  have he := runTraceMeasured_emission store a b pc hp depth
  have hp := runTraceMeasured_primitive store a b pc hp depth
  omega

theorem sampleTraceMeasured_total (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (sampleTraceMeasured store word pc hp depth).1.1.2+(sampleTraceMeasured store word pc hp depth).1.2+
      (sampleTraceMeasured store word pc hp depth).2 ≤ 15*(sampleTraceMeasured store word pc hp depth).1.1.2 := by
  have he := sampleTraceMeasured_emission store word pc hp depth
  have hp := sampleTraceMeasured_primitive store word pc hp depth
  omega

theorem run_emit_frames {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.emitFrames (runPlanAt store a b pc hp depth).1.1.2 ≤
      2*(runPlanAt store a b pc hp depth).1.2+1 := by
  have h := BinaryTracePlanMeasured.emitFrames_bound (runPlanAt store a b pc hp depth).1.1.2
  have hb := runPlanAt_budget store a b pc hp depth
  omega

theorem sample_emit_frames (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.emitFrames (samplePlanAt store word pc hp depth).1.1.2 ≤
      2*(samplePlanAt store word pc hp depth).1.2+1 := by
  have h := BinaryTracePlanMeasured.emitFrames_bound (samplePlanAt store word pc hp depth).1.1.2
  have hb := samplePlanAt_budget store word pc hp depth
  omega

theorem run_plan_references {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.planReferences (runPlanAt store a b pc hp depth).1.1.2 ≤
      4*(runPlanAt store a b pc hp depth).1.2 := by
  have h := BinaryTracePlanMeasured.planReferences_bound (runPlanAt store a b pc hp depth).1.1.2
  have hb := runPlanAt_budget store a b pc hp depth
  omega

theorem sample_plan_references (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    BinaryTracePlanMeasured.planReferences (samplePlanAt store word pc hp depth).1.1.2 ≤
      4*(samplePlanAt store word pc hp depth).1.2 := by
  have h := BinaryTracePlanMeasured.planReferences_bound (samplePlanAt store word pc hp depth).1.1.2
  have hb := samplePlanAt_budget store word pc hp depth
  omega

theorem run_shift_primitives {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (BinaryTracePlanMeasured.emitFull (runPlanAt store a b pc hp depth).1.1.2 []).2 ≤
      2*(runPlanAt store a b pc hp depth).1.2 := by
  rw [BinaryTracePlanMeasured.emitFull_shifts]
  have h := BinaryTracePlanMeasured.shiftCount_bound (runPlanAt store a b pc hp depth).1.1.2
  have hb := runPlanAt_budget store a b pc hp depth
  omega

theorem sample_shift_primitives (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    (BinaryTracePlanMeasured.emitFull (samplePlanAt store word pc hp depth).1.1.2 []).2 ≤
      2*(samplePlanAt store word pc hp depth).1.2 := by
  rw [BinaryTracePlanMeasured.emitFull_shifts]
  have h := BinaryTracePlanMeasured.shiftCount_bound (samplePlanAt store word pc hp depth).1.1.2
  have hb := samplePlanAt_budget store word pc hp depth
  omega

theorem run_emission_width {w : ℕ} (store : Store) (a b : FixedBinaryWord w)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    binaryWordWidth (runTraceMeasured store a b pc hp depth).2 ≤
      binaryWordWidth (10*(runTraceMeasured store a b pc hp depth).1.1.2) :=
  binaryWordWidth_mono (runTraceMeasured_emission store a b pc hp depth)

theorem sample_emission_width (store : Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    binaryWordWidth (sampleTraceMeasured store word pc hp depth).2 ≤
      binaryWordWidth (10*(sampleTraceMeasured store word pc hp depth).1.1.2) :=
  binaryWordWidth_mono (sampleTraceMeasured_emission store word pc hp depth)

end Blotto.BinaryWordCoinSourceMeasured
