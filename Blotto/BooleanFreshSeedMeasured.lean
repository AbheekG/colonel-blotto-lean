import Blotto.BooleanFreshBitSeedLoop
import Blotto.BinarySeedCursorMeasured
import Blotto.BooleanFreshCounterWork

/-! One Boolean countdown execution returns data, allocation trace and
source work. Each fresh-bit primitive call costs one named operation within
the fixed iteration charge; primitive internals and native observer evaluation
are separate. Numerical counter interpretation is used only in proofs. -/

namespace Blotto.BooleanFreshSeedMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTraceDepth
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scanAt : List Bool → ℕ → (Bool × Trace) × ℕ
  | [],depth => ((false,[.frames (depth+1),.arrayAllocation 4]),4)
  | true::_,depth => ((true,[.frames (depth+1),.arrayAllocation 4]),4)
  | false::rest,depth =>
      let later := scanAt rest (depth+1)
      ((later.1.1,.frames (depth+1)::.arrayAllocation 4::later.1.2),later.2+4)

theorem scanAt_erases (bits : List Bool) (depth : ℕ) :
    (scanAt bits depth).1 =
      ((BinaryBooleanPrimitiveLifetime.scanWithTrace bits).1,
        under depth (BinaryBooleanPrimitiveLifetime.scanWithTrace bits).2) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit with
    | false =>
        simp only [scanAt,BinaryBooleanPrimitiveLifetime.scanWithTrace,
          Bool.false_eq_true,ite_false,ih,under_append,under_compose]
        rfl
    | true => rfl

def scan (bits : List Bool) : (Bool × Trace) × ℕ := scanAt bits 0

theorem scan_erases (bits : List Bool) :
    (scan bits).1 = BinaryBooleanPrimitiveLifetime.scanWithTrace bits := by
  rw [scan,scanAt_erases,under_zero]

theorem scanAt_work (bits : List Bool) (depth : ℕ) :
    (scanAt bits depth).2 = 4*BooleanFreshCounterWork.scanVisits bits := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [scanAt,BooleanFreshCounterWork.scanVisits,ih] <;> omega

theorem scan_work (bits : List Bool) :
    (scan bits).2 = 4*BooleanFreshCounterWork.scanVisits bits := by
  exact scanAt_work bits 0

theorem scan_bound (bits : List Bool) : (scan bits).2 ≤ 4*(bits.length+1) := by
  rw [scan_work]
  exact Nat.mul_le_mul_left 4 (BooleanFreshCounterWork.scanVisits_bound bits)

theorem scanAt_trace_length (bits : List Bool) (depth : ℕ) :
    (scanAt bits depth).1.2.length ≤ 2*(bits.length+1) := by
  induction bits generalizing depth with
  | nil => simp [scanAt]
  | cons bit rest ih => cases bit with
    | false =>
        have h := ih (depth+1)
        simp only [scanAt,List.length_cons] at h ⊢
        omega
    | true => simp [scanAt]

theorem scanAt_frames (bits : List Bool) (depth : ℕ) :
    framePeak (scanAt bits depth).1.2 ≤ depth+bits.length+1 := by
  induction bits generalizing depth with
  | nil => simp [scanAt,framePeak]
  | cons bit rest ih => cases bit with
    | false =>
        have h := ih (depth+1)
        simp only [scanAt,framePeak,List.length_cons] at h ⊢
        omega
    | true => simp [scanAt,framePeak]

def predecessorAt : List Bool → ℕ → (List Bool × Trace) × ℕ
  | [],depth => (([],[.frames (depth+1),.arrayAllocation 8]),4)
  | true::rest,depth => ((false::rest,[.frames (depth+1),.arrayAllocation 8,.listAllocation 1]),4)
  | false::rest,depth =>
      let later := predecessorAt rest (depth+1)
      ((true::later.1.1,.frames (depth+1)::.arrayAllocation 8::.listAllocation 1::later.1.2),later.2+4)

theorem predecessorAt_erases (bits : List Bool) (depth : ℕ) :
    (predecessorAt bits depth).1 =
      ((BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace bits).1,
        under depth (BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace bits).2) := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit with
    | false =>
        simp only [predecessorAt,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace,
          ih,under_append,under_compose]
        rfl
    | true => rfl

def predecessor (bits : List Bool) : (List Bool × Trace) × ℕ := predecessorAt bits 0

theorem predecessor_erases (bits : List Bool) :
    (predecessor bits).1 = BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace bits := by
  rw [predecessor,predecessorAt_erases,under_zero]

theorem predecessorAt_work (bits : List Bool) (depth : ℕ) :
    (predecessorAt bits depth).2 = 4*BinaryStoredCountdown.predecessorVisits bits := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [predecessorAt,BinaryStoredCountdown.predecessorVisits,ih] <;> omega

theorem predecessor_work (bits : List Bool) :
    (predecessor bits).2 = 4*BinaryStoredCountdown.predecessorVisits bits := by
  exact predecessorAt_work bits 0

theorem predecessor_bound (bits : List Bool) : (predecessor bits).2 ≤ 4*(bits.length+1) := by
  rw [predecessor_work]
  exact Nat.mul_le_mul_left 4 (BinaryStoredCountdown.predecessorVisits_bound bits)

theorem predecessorAt_trace_length (bits : List Bool) (depth : ℕ) :
    (predecessorAt bits depth).1.2.length ≤ 3*bits.length+2 := by
  induction bits generalizing depth with
  | nil => simp [predecessorAt]
  | cons bit rest ih => cases bit with
    | false =>
        have h := ih (depth+1)
        simp only [predecessorAt,List.length_cons] at h ⊢
        omega
    | true => simp [predecessorAt]; omega

theorem predecessorAt_frames (bits : List Bool) (depth : ℕ) :
    framePeak (predecessorAt bits depth).1.2 ≤ depth+bits.length+1 := by
  induction bits generalizing depth with
  | nil => simp [predecessorAt,framePeak]
  | cons bit rest ih => cases bit with
    | false =>
        have h := ih (depth+1)
        simp only [predecessorAt,framePeak,List.length_cons] at h ⊢
        omega
    | true => simp [predecessorAt,framePeak]

-- Child traces already carry their absolute depths. Appending the two local
-- primitive traces never copies the recursively returned generation trace.
def loopAt {S : Type*} (next : S → Bool × S) (counter reversed : List Bool)
    (state : S) (depth : ℕ) : ((List Bool × S) × Trace) × ℕ :=
  let tested := scanAt counter (depth+2)
  if h : tested.1.1 = true then
    let bit := next state
    let decremented := predecessorAt counter (depth+2)
    let later := loopAt next decremented.1.1 (bit.1::reversed) bit.2 (depth+2)
    ((later.1.1,.listAllocation 1::.frames (depth+2)::.arrayAllocation 32::
      (tested.1.2++(decremented.1.2++later.1.2))),
      tested.2+decremented.2+later.2+8)
  else
    let result := BinarySeedCursorMeasured.reverseAt reversed [] (depth+2)
    (((result.1.1,state),.frames (depth+2)::.arrayAllocation 24::
      (tested.1.2++result.1.2)),tested.2+result.2+4)
termination_by BinaryBigEndian.littleValue counter
decreasing_by
  have hp : 0 < BinaryBigEndian.littleValue counter := by
    apply (BinaryEuclideanGCD.nonzero_true_iff counter).mp
    change (scanAt counter (depth+2)).1.1 = true at h
    simpa only [scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using h
  rw [predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
  have hd := BinaryStoredCountdown.predecessor_value counter hp
  omega

theorem loopAt_erases {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopAt next counter reversed state depth).1 =
      ((BooleanFreshBitSeedLoop.loopWithTrace next counter reversed state).1,
        under depth (BooleanFreshBitSeedLoop.loopWithTrace next counter reversed state).2) := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      (loopAt next counter reversed state depth).1 =
        ((BooleanFreshBitSeedLoop.loopWithTrace next counter reversed state).1,
          under depth (BooleanFreshBitSeedLoop.loopWithTrace next counter reversed state).2) := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        rw [loopAt,BooleanFreshBitSeedLoop.loopWithTrace]
        dsimp only
        simp only [scanAt_erases]
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          simp only [predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          rw [ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)]
          simp only [wrapList,wrap,combine,under_append,under_compose,List.append_nil]
          rfl
        · simp only [BinarySeedCursorMeasured.reverseAt_erases,wrap,combine,
            under_append,under_compose,List.append_nil]
          rfl
  exact hAll _ counter rfl reversed state depth

def loop {S : Type*} (next : S → Bool × S) (counter reversed : List Bool) (state : S) :
    ((List Bool × S) × Trace) × ℕ := loopAt next counter reversed state 0

theorem loop_erases {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) :
    (loop next counter reversed state).1 =
      BooleanFreshBitSeedLoop.loopWithTrace next counter reversed state := by
  rw [loop,loopAt_erases,under_zero]

theorem loopAt_work {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopAt next counter reversed state depth).2 ≤
      32*(counter.length+1)*(BinaryBigEndian.littleValue counter+1)+4*reversed.length+16 := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      (loopAt next counter reversed state depth).2 ≤
        32*(counter.length+1)*(count+1)+4*reversed.length+16 := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        have hScan : (scanAt counter (depth+2)).2 ≤ 4*(counter.length+1) := by
          rw [scanAt_work]
          exact Nat.mul_le_mul_left 4 (BooleanFreshCounterWork.scanVisits_bound counter)
        rw [loopAt]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          have hl := ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)
          have hPred : (predecessorAt counter (depth+2)).2 ≤ 4*(counter.length+1) := by
            rw [predecessorAt_work]
            exact Nat.mul_le_mul_left 4 (BinaryStoredCountdown.predecessorVisits_bound counter)
          rw [predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          rw [BinaryStoredCountdown.predecessor_length] at hl
          simp only [List.length_cons] at hl
          nlinarith
        · have hr := BinarySeedCursorMeasured.reverseAt_work reversed [] (depth+2)
          rw [BinaryMidpointTapeLifetime.reverse_work] at hr
          nlinarith
  exact hAll _ counter rfl reversed state depth

theorem loop_work {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) :
    (loop next counter reversed state).2 ≤
      32*(counter.length+1)*(BinaryBigEndian.littleValue counter+1)+4*reversed.length+16 :=
  loopAt_work next counter reversed state 0

def generate {S : Type*} (next : S → Bool × S) (counter : List Bool) (state : S) :
    ((List Bool × S) × Trace) × ℕ := loop next counter [] state

theorem generate_erases {S : Type*} (next : S → Bool × S) (counter : List Bool) (state : S) :
    (generate next counter state).1 =
      BooleanFreshBitSeedLoop.generateWithTrace next counter state := loop_erases next counter [] state

theorem generate_work {S : Type*} (next : S → Bool × S) (counter : List Bool) (state : S) :
    (generate next counter state).2 ≤
      32*(counter.length+1)*(BinaryBigEndian.littleValue counter+1)+16 := by
  simpa only [generate,List.length_nil,mul_zero,Nat.add_zero] using loop_work next counter [] state

theorem generate_counted {S : Type*} (next : S → Bool × S)
    (counter : List Bool) (state : S) (calls : ℕ) :
    (generate (FreshBitSeedLifetime.countedFresh next) counter (state,calls)).1.1 =
      ((generate next counter state).1.1.1,((generate next counter state).1.1.2,
        calls+BinaryBigEndian.littleValue counter)) := by
  simp only [generate_erases,BooleanFreshBitSeedLoop.generate_counted]

end Blotto.BooleanFreshSeedMeasured
