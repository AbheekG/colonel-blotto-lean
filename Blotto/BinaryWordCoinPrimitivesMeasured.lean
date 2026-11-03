import Blotto.BinaryWordCoinLifetime
import Blotto.BinaryDivisionMeasured
import Blotto.BinaryDivisionStorageMeasured
import Blotto.BinaryBorrowSummaryMeasured
import Blotto.BooleanFreshSeedMeasured

/-! Reached Boolean coin primitives return old data/traces and source work.
Scan/equality/tree/increment/padding loops are structural; restoring residuals
and the guard now consume storage-fused producers. Separate returned primitive
charges have factor-four/two bounds against the old compatibility counters.
The guard computes Boolean borrow alone with a cached-width summary; its full
old measured record is preserved. Reached tree scan, lookup, carry, replication,
append and padding traces emit absolute depths directly. Their recursive tails
are never shifted or recopied on return; lookup/pad join two local traces once.
Native reference/observer/index-arithmetic/allocator prices remain separate. -/

namespace Blotto.BinaryWordCoinPrimitivesMeasured
open BinarySeedPreparationSpace BinarySeedLookupTree BinaryRationalNormalization
set_option autoImplicit false
set_option maxHeartbeats 3000000

def zero (bits : List Bool) : (Bool × Trace) × ℕ :=
  let result := BooleanFreshSeedMeasured.scan bits
  ((!result.1.1,result.1.2),result.2+2)

theorem zero_erases (bits : List Bool) : (zero bits).1 = BinaryWordCoinLifetime.zeroWithTrace bits := by
  simp only [zero,BinaryWordCoinLifetime.zeroWithTrace,BooleanFreshSeedMeasured.scan_erases]

theorem zero_work (bits : List Bool) : (zero bits).2 ≤ 4*(bits.length+1)+2 := by
  have h := BooleanFreshSeedMeasured.scan_bound bits
  change _+2 ≤ _
  omega

def same : List Bool → List Bool → (Bool × Trace) × ℕ
  | [],[] => ((true,[.frames 1,.arrayAllocation 4]),6)
  | a::rest,b::tail =>
      if a=b then
        let later := same rest tail
        ((later.1.1,[.frames 1,.arrayAllocation 4]++under 1 later.1.2),later.2+6)
      else ((false,[.frames 1,.arrayAllocation 4]),6)
  | _,_ => ((false,[.frames 1,.arrayAllocation 4]),6)

theorem same_erases (first second : List Bool) : (same first second).1 = BinaryWordCoinLifetime.sameWithTrace first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail => simp only [same,BinaryWordCoinLifetime.sameWithTrace,ih]; split <;> rfl

theorem same_work (first second : List Bool) : (same first second).2 ≤ 6*(first.length+1) := by
  induction first generalizing second with
  | nil => cases second <;> simp [same]
  | cons bit rest ih => cases second with
    | nil => simp [same]
    | cons other tail =>
        have h := ih tail
        simp only [same,List.length_cons]
        split <;> simp only <;> omega

def scanTreeAt : {height : ℕ} → Tree height → List Bool → ℕ → (Bool × Trace) × ℕ
  | _,.leaf bit,_,depth => ((bit,[.frames (depth+1),.arrayAllocation 4]),4)
  | _,.branch left _,[],depth =>
      let later := scanTreeAt left [] (depth+1)
      ((later.1.1,.frames (depth+1)::.arrayAllocation 4::later.1.2),later.2+4)
  | _,.branch left right,bit::rest,depth =>
      let later := if bit then scanTreeAt right rest (depth+1) else scanTreeAt left rest (depth+1)
      ((later.1.1,.frames (depth+1)::.arrayAllocation 4::later.1.2),later.2+4)

theorem scanTreeAt_erases {height : ℕ} (tree : Tree height) (address : List Bool) (depth : ℕ) :
    (scanTreeAt tree address depth).1 =
      ((BinaryWordStoreLifetime.scanTreeWithTrace tree address).1,
        under depth (BinaryWordStoreLifetime.scanTreeWithTrace tree address).2) := by
  induction tree generalizing address depth with
  | leaf bit => rfl
  | branch left right hl hr =>
      cases address with
      | nil =>
          simp only [scanTreeAt,BinaryWordStoreLifetime.scanTreeWithTrace,hl,
            BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose]
          rfl
      | cons bit rest =>
          cases bit <;> simp only [scanTreeAt,BinaryWordStoreLifetime.scanTreeWithTrace,
            Bool.false_eq_true,ite_true,ite_false,hl,hr,
            BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose] <;> rfl

theorem scanTreeAt_work {height : ℕ} (tree : Tree height) (address : List Bool) (depth : ℕ) :
    (scanTreeAt tree address depth).2 = 4*(height+1) := by
  induction tree generalizing address depth with
  | leaf bit => rfl
  | branch left right hl hr => cases address with
    | nil => simp only [scanTreeAt,hl]; omega
    | cons bit rest => cases bit <;> simp only [scanTreeAt,Bool.false_eq_true,ite_true,ite_false,hl,hr] <;> omega

theorem scanTreeAt_trace_length {height : ℕ} (tree : Tree height) (address : List Bool) (depth : ℕ) :
    (scanTreeAt tree address depth).1.2.length = 2*(height+1) := by
  induction tree generalizing address depth with
  | leaf bit => rfl
  | branch left right hl hr => cases address with
    | nil => simp only [scanTreeAt,List.length_cons,hl]; omega
    | cons bit rest => cases bit <;> simp only [scanTreeAt,Bool.false_eq_true,ite_true,ite_false,
        List.length_cons,hl,hr] <;> omega

def scanTree {height : ℕ} (tree : Tree height) (address : List Bool) : (Bool × Trace) × ℕ :=
  scanTreeAt tree address 0

theorem scanTree_erases {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    (scanTree tree address).1 = BinaryWordStoreLifetime.scanTreeWithTrace tree address := by
  simpa only [scanTree,BinaryTraceDepth.under_zero] using scanTreeAt_erases tree address 0

theorem scanTree_work {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    (scanTree tree address).2 = 4*(depth+1) := by
  exact scanTreeAt_work tree address 0

def lookupAt (store : Store) (address : FixedBinaryWord store.width) (depth : ℕ) : (Bool × Trace) × ℕ :=
  let reversed := BinarySeedCursorMeasured.reverseAt address.bits [] (depth+2)
  let reached := scanTreeAt store.tree reversed.1.1 (depth+2)
  ((reached.1.1,.frames (depth+2)::.arrayAllocation 8::(reversed.1.2++reached.1.2)),
    reversed.2+reached.2+4)

theorem lookupAt_erases (store : Store) (address : FixedBinaryWord store.width) (depth : ℕ) :
    (lookupAt store address depth).1 =
      ((BinaryWordStoreLifetime.lookupWithTrace store address).1,
        under depth (BinaryWordStoreLifetime.lookupWithTrace store address).2) := by
  simp only [lookupAt,BinaryWordStoreLifetime.lookupWithTrace,scanTreeAt_erases,
    BinarySeedCursorMeasured.reverseAt_erases,BinaryTraceDepth.under_append,BinaryTraceDepth.under_compose]
  rfl

theorem lookupAt_work (store : Store) (address : FixedBinaryWord store.width) (depth : ℕ) :
    (lookupAt store address depth).2 = 8*store.width+10 := by
  simp only [lookupAt,scanTreeAt_work,BinarySeedCursorMeasured.reverseAt_work,
    BinaryMidpointTapeLifetime.reverse_work,address.size]
  omega

theorem lookupAt_trace_length (store : Store) (address : FixedBinaryWord store.width) (depth : ℕ) :
    (lookupAt store address depth).1.2.length = 4*store.width+5 := by
  simp only [lookupAt,List.length_cons,List.length_append,BinarySeedCursorMeasured.reverseAt_trace_length,
    scanTreeAt_trace_length,address.size]
  omega

def lookup (store : Store) (address : FixedBinaryWord store.width) : (Bool × Trace) × ℕ :=
  lookupAt store address 0

theorem lookup_erases (store : Store) (address : FixedBinaryWord store.width) :
    (lookup store address).1 = BinaryWordStoreLifetime.lookupWithTrace store address := by
  simpa only [lookup,BinaryTraceDepth.under_zero] using lookupAt_erases store address 0

theorem lookup_work (store : Store) (address : FixedBinaryWord store.width) :
    (lookup store address).2 = 8*store.width+10 := by
  exact lookupAt_work store address 0

theorem under_compose (first second : ℕ) (trace : Trace) :
    under first (under second trace) = under (first+second) trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [under,shiftEvent,Nat.add_assoc] at ih ⊢ <;> exact ih

theorem under_append_exact (depth : ℕ) (first second : Trace) :
    under depth (first++second) = under depth first++under depth second := by
  simp only [under,List.map_append]

theorem under_zero (trace : Trace) : under 0 trace = trace := by
  induction trace with
  | nil => rfl
  | cons event rest ih => cases event <;> simp [under,shiftEvent] at ih ⊢ <;> exact ih

def incrementBitsAt : List Bool → ℕ → ((List Bool × Bool) × Trace) × ℕ
  | [],depth => ((([],true),[.frames (depth+1),.arrayAllocation 4]),4)
  | false::rest,depth => (((true::rest,false),[.frames (depth+1),.listAllocation 1,.arrayAllocation 4]),4)
  | true::rest,depth =>
      let later := incrementBitsAt rest (depth+1)
      (((false::later.1.1.1,later.1.1.2),.frames (depth+1)::.listAllocation 1::.arrayAllocation 4::later.1.2),later.2+4)

theorem incrementBitsAt_erases (bits : List Bool) (depth : ℕ) :
    (incrementBitsAt bits depth).1 =
      ((BinaryWordStoreLifetime.incrementBitsWithTrace bits).1,
        under depth (BinaryWordStoreLifetime.incrementBitsWithTrace bits).2) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit with
    | false => rfl
    | true =>
        simp only [incrementBitsAt,BinaryWordStoreLifetime.incrementBitsWithTrace,ih,
          under_append_exact,under_compose]
        rfl

def incrementBits (bits : List Bool) : ((List Bool × Bool) × Trace) × ℕ := incrementBitsAt bits 0

theorem incrementBits_erases (bits : List Bool) :
    (incrementBits bits).1 = BinaryWordStoreLifetime.incrementBitsWithTrace bits := by
  rw [incrementBits,incrementBitsAt_erases]
  rw [under_zero]

theorem incrementBitsAt_work (bits : List Bool) (depth : ℕ) :
    (incrementBitsAt bits depth).2 = 4*BinaryIndexWord.incrementVisits bits := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [incrementBitsAt,BinaryIndexWord.incrementVisits,ih] <;> omega

theorem incrementBits_work (bits : List Bool) : (incrementBits bits).2 ≤ 4*(bits.length+1) := by
  rw [incrementBits,incrementBitsAt_work]
  exact Nat.mul_le_mul_left 4 (BinaryIndexWord.incrementVisits_bound bits)

theorem incrementBitsAt_trace_length (bits : List Bool) (depth : ℕ) :
    (incrementBitsAt bits depth).1.2.length ≤ 3*(bits.length+1) := by
  induction bits generalizing depth with
  | nil => simp [incrementBitsAt]
  | cons bit rest ih =>
      cases bit
      · simp only [incrementBitsAt,List.length_cons,List.length_nil]; omega
      · have h := ih (depth+1)
        simp only [incrementBitsAt,List.length_cons]
        omega

theorem incrementBitsAt_frames (bits : List Bool) (depth : ℕ) :
    framePeak (incrementBitsAt bits depth).1.2 ≤ depth+bits.length+1 := by
  induction bits generalizing depth with
  | nil => simp [incrementBitsAt,framePeak]
  | cons bit rest ih =>
      cases bit
      · simp only [incrementBitsAt,framePeak,List.length_cons]; omega
      · have h := ih (depth+1)
        simp only [incrementBitsAt,framePeak,List.length_cons]
        omega

def incrementAt {w : ℕ} (word : FixedBinaryWord w) (depth : ℕ) : ((FixedBinaryWord w × Bool) × Trace) × ℕ :=
  let next := incrementBitsAt word.bits (depth+2)
  have hSize : next.1.1.1.length = w := by
    rw [incrementBitsAt_erases,BinaryWordStoreLifetime.incrementBitsWithTrace_erases,BinaryIndexWord.incrementBits_length,word.size]
  (((⟨next.1.1.1,hSize⟩,next.1.1.2),.frames (depth+2)::.arrayAllocation 8::next.1.2),next.2+2*w+4)

theorem incrementAt_erases {w : ℕ} (word : FixedBinaryWord w) (depth : ℕ) :
    (incrementAt word depth).1 =
      ((BinaryWordStoreLifetime.incrementWithTrace word).1,
        under depth (BinaryWordStoreLifetime.incrementWithTrace word).2) := by
  simp only [incrementAt,BinaryWordStoreLifetime.incrementWithTrace,incrementBitsAt_erases,
    under_append_exact,under_compose]
  rfl

theorem incrementAt_work {w : ℕ} (word : FixedBinaryWord w) (depth : ℕ) :
    (incrementAt word depth).2 = 4*BinaryIndexWord.incrementVisits word.bits+2*w+4 := by
  simp only [incrementAt,incrementBitsAt_work]

theorem incrementAt_trace_length {w : ℕ} (word : FixedBinaryWord w) (depth : ℕ) :
    (incrementAt word depth).1.2.length ≤ 3*(w+1)+2 := by
  have h := incrementBitsAt_trace_length word.bits (depth+2)
  simp only [incrementAt,List.length_cons]
  rw [word.size] at h
  omega

def increment {w : ℕ} (word : FixedBinaryWord w) : ((FixedBinaryWord w × Bool) × Trace) × ℕ :=
  incrementAt word 0

theorem increment_erases {w : ℕ} (word : FixedBinaryWord w) :
    (increment word).1 = BinaryWordStoreLifetime.incrementWithTrace word := by
  simpa only [increment,under_zero] using incrementAt_erases word 0

theorem increment_work {w : ℕ} (word : FixedBinaryWord w) : (increment word).2 ≤ 6*w+8 := by
  have h := BinaryIndexWord.incrementVisits_bound word.bits
  rw [word.size] at h
  rw [increment,incrementAt_work]
  omega

def ltMeasuredReference {w : ℕ} (first second : FixedBinaryWord w) : ((Bool × Trace) × ℕ) × ℕ :=
  let result := BinaryCompareBitsMeasured.borrow first.bits second.bits false []
  (((result.data.2,[.frames (2*w+4),.arrayAllocation 8,.listAllocation result.storage]),16*(w+1)),result.work)

def ltMeasured {w : ℕ} (first second : FixedBinaryWord w) : ((Bool × Trace) × ℕ) × ℕ :=
  let result := BinaryBorrowSummaryMeasured.run first.bits second.bits false w 0
  (((result.answer,[.frames (2*w+4),.arrayAllocation 8,
    .listAllocation (result.held+result.allocated)]),16*(w+1)),22*(w+1))

theorem ltMeasured_eq_reference {w : ℕ} (first second : FixedBinaryWord w) :
    ltMeasured first second = ltMeasuredReference first second := by
  have h := BinaryCompareBitsMeasured.borrow_work first.bits second.bits false []
    (first.size.trans second.size.symm)
  simp only [first.size,List.length_nil,mul_zero,Nat.add_zero] at h
  simp only [ltMeasured,ltMeasuredReference,BinaryBorrowSummaryMeasured.run_data,
    BinaryBorrowSummaryMeasured.run_storage first.bits second.bits w first.size second.size,
    BinaryCompareBitsMeasured.borrow_data,BinaryCompareBitsMeasured.borrow_storage,h]

def lt {w : ℕ} (first second : FixedBinaryWord w) : (Bool × Trace) × ℕ :=
  (ltMeasured first second).1

theorem ltMeasured_compat {w : ℕ} (first second : FixedBinaryWord w) :
    (ltMeasured first second).1 = lt first second := rfl

theorem lt_erases {w : ℕ} (first second : FixedBinaryWord w) :
    (lt first second).1 = BinaryWordStoreLifetime.ltWithTrace first second := by
  simp only [lt,ltMeasured_eq_reference,ltMeasuredReference,BinaryWordStoreLifetime.ltWithTrace,
    BinaryCompareBitsMeasured.borrow_data,BinaryCompareBitsMeasured.borrow_storage,
    BinaryDivisionAllocation.borrowWithAllocation_refines]

theorem lt_source_work {w : ℕ} (first second : FixedBinaryWord w) :
    (BinaryIndexWord.ltWithWork first second).2+4 ≤ (lt first second).2 := by
  have h := BinaryIndexWord.ltWithWork_bound first second
  change _+4 ≤ 16*(w+1)
  omega

theorem ltMeasured_work_bound {w : ℕ} (first second : FixedBinaryWord w) :
    (ltMeasured first second).2 ≤ 2*(lt first second).2 := by
  change 22*(w+1) ≤ 2*(16*(w+1))
  omega

theorem ltMeasured_scan_work {w : ℕ} (first second : FixedBinaryWord w) :
    (BinaryBorrowSummaryMeasured.run first.bits second.bits false w 0).work ≤ (ltMeasured first second).2 :=
  BinaryBorrowSummaryMeasured.run_work_bound first.bits second.bits w first.size second.size

def stepMeasured {w : ℕ} (a b : FixedBinaryWord w) : (((Bool × FixedBinaryWord w) × Trace) × ℕ) × ℕ :=
  let stepped := BinaryDivisionStorageMeasured.step false a.bits b.bits
  have hSize : stepped.data.2.length = w := by
    rw [BinaryDivisionStorageMeasured.step_data]
    exact (BinaryDivisionWord.step_length false a.bits b.bits (a.size.trans b.size.symm)).trans a.size
  ((((stepped.data.1,⟨stepped.data.2,hSize⟩),[.frames (2*w+8),.arrayAllocation 8,
    .listAllocation stepped.storage]),stepped.source+4),stepped.work+4)

def step {w : ℕ} (a b : FixedBinaryWord w) : ((Bool × FixedBinaryWord w) × Trace) × ℕ :=
  (stepMeasured a b).1

theorem stepMeasured_compat {w : ℕ} (a b : FixedBinaryWord w) :
    (stepMeasured a b).1 = step a b := rfl

theorem step_erases {w : ℕ} (a b : FixedBinaryWord w) :
    (step a b).1 = BinaryWordCoinLifetime.stepWithTrace a b := by
  simp only [step,stepMeasured,BinaryWordCoinLifetime.stepWithTrace,
    ← BinaryDivisionStorageMeasured.step_erases,BinaryDivisionStorageMeasured.step_storage]

theorem step_work {w : ℕ} (a b : FixedBinaryWord w) : (step a b).2 ≤ 17*w+24 := by
  have h := BinaryDivisionWord.bitWork_bound false a.bits b.bits (a.size.trans b.size.symm)
  rw [a.size] at h
  simp only [step,stepMeasured,BinaryDivisionStorageMeasured.step_source_work]
  omega

theorem stepMeasured_work_bound {w : ℕ} (a b : FixedBinaryWord w) :
    (stepMeasured a b).2 ≤ 4*(step a b).2 := by
  have h := BinaryDivisionStorageMeasured.step_work_bound false a.bits b.bits (a.size.trans b.size.symm)
  simp only [step,stepMeasured]
  omega

def replicateAt : ℕ → Bool → ℕ → (List Bool × Trace) × ℕ
  | 0,_,depth => (([],[.frames (depth+1)]),2)
  | n+1,bit,depth =>
      let later := replicateAt n bit (depth+1)
      ((bit::later.1.1,.frames (depth+1)::.listAllocation 1::later.1.2),later.2+4)

theorem replicateAt_erases (n : ℕ) (bit : Bool) (depth : ℕ) :
    (replicateAt n bit depth).1 =
      ((BinaryPRGOutputLifetime.replicateWithTrace n bit).1,
        under depth (BinaryPRGOutputLifetime.replicateWithTrace n bit).2) := by
  induction n generalizing depth with
  | zero => rfl
  | succ n ih =>
      simp only [replicateAt,BinaryPRGOutputLifetime.replicateWithTrace,ih,under_append_exact,under_compose]
      rfl

theorem replicateAt_work (n : ℕ) (bit : Bool) (depth : ℕ) : (replicateAt n bit depth).2 = 4*n+2 := by
  induction n generalizing depth with
  | zero => rfl
  | succ n ih => simp only [replicateAt,ih]; omega

theorem replicateAt_trace_length (n : ℕ) (bit : Bool) (depth : ℕ) :
    (replicateAt n bit depth).1.2.length = 2*n+1 := by
  induction n generalizing depth with
  | zero => rfl
  | succ n ih => simp only [replicateAt,List.length_cons,ih]; omega

def replicate (n : ℕ) (bit : Bool) : (List Bool × Trace) × ℕ := replicateAt n bit 0

theorem replicate_erases (n : ℕ) (bit : Bool) :
    (replicate n bit).1 = BinaryPRGOutputLifetime.replicateWithTrace n bit := by
  simpa only [replicate,under_zero] using replicateAt_erases n bit 0

theorem replicate_work (n : ℕ) (bit : Bool) : (replicate n bit).2 = 4*n+2 := by
  exact replicateAt_work n bit 0

def appendAt : List Bool → List Bool → ℕ → (List Bool × Trace) × ℕ
  | [],right,depth => ((right,[.frames (depth+1)]),2)
  | bit::left,right,depth =>
      let later := appendAt left right (depth+1)
      ((bit::later.1.1,.frames (depth+1)::.listAllocation 1::later.1.2),later.2+4)

theorem appendAt_erases (left right : List Bool) (depth : ℕ) :
    (appendAt left right depth).1 =
      ((BinaryPRGOutputLifetime.appendWithTrace left right).1,
        under depth (BinaryPRGOutputLifetime.appendWithTrace left right).2) := by
  induction left generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      simp only [appendAt,BinaryPRGOutputLifetime.appendWithTrace,ih,under_append_exact,under_compose]
      rfl

theorem appendAt_work (left right : List Bool) (depth : ℕ) : (appendAt left right depth).2 = 4*left.length+2 := by
  induction left generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [appendAt,List.length_cons,ih]; omega

theorem appendAt_trace_length (left right : List Bool) (depth : ℕ) :
    (appendAt left right depth).1.2.length = 2*left.length+1 := by
  induction left generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [appendAt,List.length_cons,ih]; omega

def append (left right : List Bool) : (List Bool × Trace) × ℕ := appendAt left right 0

theorem append_erases (left right : List Bool) :
    (append left right).1 = BinaryPRGOutputLifetime.appendWithTrace left right := by
  simpa only [append,under_zero] using appendAt_erases left right 0

theorem append_work (left right : List Bool) : (append left right).2 = 4*left.length+2 := by
  exact appendAt_work left right 0

def padAt (W : ℕ) (bits : List Bool) (depth : ℕ) : (List Bool × Trace) × ℕ :=
  let zeros := replicateAt (W-bits.length) false (depth+2)
  let joined := appendAt bits zeros.1.1 (depth+2)
  ((joined.1.1,.frames (depth+2)::.arrayAllocation 8::(zeros.1.2++joined.1.2)),
    zeros.2+joined.2+2*bits.length+4)

theorem padAt_erases (W : ℕ) (bits : List Bool) (depth : ℕ) :
    (padAt W bits depth).1 =
      ((BinaryWordCoinLifetime.padWithTrace W bits).1,
        under depth (BinaryWordCoinLifetime.padWithTrace W bits).2) := by
  simp only [padAt,BinaryWordCoinLifetime.padWithTrace,replicateAt_erases,appendAt_erases,
    under_append_exact,under_compose]
  rfl

theorem padAt_work (W : ℕ) (bits : List Bool) (depth : ℕ) :
    (padAt W bits depth).2 = 4*(W-bits.length)+6*bits.length+8 := by
  simp only [padAt,replicateAt_work,appendAt_work]
  omega

theorem padAt_trace_length (W : ℕ) (bits : List Bool) (depth : ℕ) (h : bits.length ≤ W) :
    (padAt W bits depth).1.2.length = 2*W+4 := by
  simp only [padAt,List.length_cons,List.length_append,replicateAt_trace_length,appendAt_trace_length]
  omega

def pad (W : ℕ) (bits : List Bool) : (List Bool × Trace) × ℕ := padAt W bits 0

theorem pad_erases (W : ℕ) (bits : List Bool) : (pad W bits).1 = BinaryWordCoinLifetime.padWithTrace W bits := by
  simpa only [pad,under_zero] using padAt_erases W bits 0

theorem pad_work (W : ℕ) (bits : List Bool) (h : bits.length ≤ W) : (pad W bits).2 ≤ 6*W+8 := by
  rw [pad,padAt_work]
  omega

end Blotto.BinaryWordCoinPrimitivesMeasured
