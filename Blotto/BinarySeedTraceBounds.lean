import Blotto.BooleanFreshSeedMeasured
import Blotto.BinaryWordWidthCore

/-! Trace-cell and scalar-depth bounds for the direct seed emitters. The
returned source counters bound emitted cells; native Nat arithmetic, record
headers and allocation/GC still need their separate machine interpretation. -/
namespace Blotto.BinarySeedTraceBounds
open BinarySeedPreparationSpace BooleanFreshSeedMeasured RationalLottoResourceSystem
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem scan_trace_length (bits : List Bool) (depth : ℕ) :
    (scanAt bits depth).1.2.length = 2*BooleanFreshCounterWork.scanVisits bits := by
  induction bits generalizing depth with
  | nil => rfl
  | cons bit rest ih => cases bit <;>
      simp only [scanAt,BooleanFreshCounterWork.scanVisits,List.length_cons,List.length_nil,ih] <;> omega

theorem scan_trace_work (bits : List Bool) (depth : ℕ) :
    (scanAt bits depth).1.2.length ≤ (scanAt bits depth).2 := by
  rw [scan_trace_length,scanAt_work]
  omega

theorem predecessor_trace_length (bits : List Bool) (depth : ℕ) :
    (predecessorAt bits depth).1.2.length ≤ 3*BinaryStoredCountdown.predecessorVisits bits := by
  induction bits generalizing depth with
  | nil => simp [predecessorAt,BinaryStoredCountdown.predecessorVisits]
  | cons bit rest ih => cases bit with
    | false =>
        have h := ih (depth+1)
        simp only [predecessorAt,BinaryStoredCountdown.predecessorVisits,List.length_cons] at h ⊢
        omega
    | true => rfl

theorem predecessor_trace_work (bits : List Bool) (depth : ℕ) :
    (predecessorAt bits depth).1.2.length ≤ (predecessorAt bits depth).2 := by
  have h := predecessor_trace_length bits depth
  rw [predecessorAt_work]
  omega

theorem reverse_trace_work (bits acc : List Bool) (depth : ℕ) :
    (BinarySeedCursorMeasured.reverseAt bits acc depth).1.2.length ≤
      (BinarySeedCursorMeasured.reverseAt bits acc depth).2 := by
  rw [BinarySeedCursorMeasured.reverseAt_trace_length,BinarySeedCursorMeasured.reverseAt_work,
    BinaryMidpointTapeLifetime.reverse_work]
  omega

-- These are exactly the two left prefixes of the reached positive branch's
-- right-associated appends. The recursively returned trace is their tail.
theorem local_append_prefixes (counter : List Bool) (depth : ℕ) :
    (scanAt counter depth).1.2.length+(predecessorAt counter depth).1.2.length ≤
      (scanAt counter depth).2+(predecessorAt counter depth).2 :=
  Nat.add_le_add (scan_trace_work counter depth) (predecessor_trace_work counter depth)

theorem loop_observers {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopAt next counter reversed state depth).1.2.length ≤
        (loopAt next counter reversed state depth).2 ∧
      framePeak (loopAt next counter reversed state depth).1.2 ≤
        depth+3*BinaryBigEndian.littleValue counter+counter.length+reversed.length+3 := by
  have hAll : ∀ count,∀ counter : List Bool,BinaryBigEndian.littleValue counter = count →
      ∀ (reversed : List Bool) (state : S) (depth : ℕ),
      (loopAt next counter reversed state depth).1.2.length ≤
          (loopAt next counter reversed state depth).2 ∧
        framePeak (loopAt next counter reversed state depth).1.2 ≤
          depth+3*count+counter.length+reversed.length+3 := by
    intro count
    induction count using Nat.strong_induction_on with
    | h count ih =>
        intro counter hCount reversed state depth
        have hScan := scan_trace_work counter (depth+2)
        have hScanFrame := scanAt_frames counter (depth+2)
        rw [loopAt]
        dsimp only
        split
        · rename_i hTest
          have hp := (BinaryEuclideanGCD.nonzero_true_iff counter).mp
            (by simpa only [scanAt_erases,BinaryBooleanPrimitiveLifetime.scanWithTrace_erases] using hTest)
          have hd := BinaryStoredCountdown.predecessor_value counter hp
          have hLess : BinaryBigEndian.littleValue (BinaryStoredCountdown.predecessor counter) < count := by omega
          have hl := ih _ hLess _ rfl ((next state).1::reversed) (next state).2 (depth+2)
          rw [BinaryStoredCountdown.predecessor_length] at hl
          simp only [List.length_cons] at hl
          have hPred := predecessor_trace_work counter (depth+2)
          have hPredFrame := predecessorAt_frames counter (depth+2)
          have hData : (predecessorAt counter (depth+2)).1.1 =
              BinaryStoredCountdown.predecessor counter := by
            rw [predecessorAt_erases,BinaryPRGHeapPrimitiveLifetime.predecessorWithTrace_erasure]
          rw [hData]
          constructor
          · simp only [List.length_cons,List.length_append]
            omega
          · simp only [framePeak,framePeak_append]
            omega
        · have hr := reverse_trace_work reversed [] (depth+2)
          have hFrame := BinarySeedCursorMeasured.reverseAt_frames reversed [] (depth+2)
          constructor
          · simp only [List.length_cons,List.length_append]
            omega
          · simp only [framePeak,framePeak_append]
            omega
  exact hAll _ counter rfl reversed state depth

theorem loop_trace_bound {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth : ℕ) :
    (loopAt next counter reversed state depth).1.2.length ≤
      32*(counter.length+1)*(BinaryBigEndian.littleValue counter+1)+4*reversed.length+16 :=
  (loop_observers next counter reversed state depth).1.trans
    (loopAt_work next counter reversed state depth)

theorem frames_le_peak (trace : Trace) (count : ℕ) (h : .frames count ∈ trace) :
    count ≤ framePeak trace := by
  induction trace with
  | nil => cases h
  | cons event rest ih =>
      rcases List.mem_cons.mp h with h | h
      · subst event
        simp [framePeak]
      · have hr := ih h
        cases event <;> simp only [framePeak] <;> omega

theorem loop_frame_width {S : Type*} (next : S → Bool × S)
    (counter reversed : List Bool) (state : S) (depth count : ℕ)
    (h : .frames count ∈ (loopAt next counter reversed state depth).1.2) :
    binaryWordWidth count ≤ binaryWordWidth
      (depth+3*BinaryBigEndian.littleValue counter+counter.length+reversed.length+3) :=
  binaryWordWidth_mono ((frames_le_peak _ count h).trans
    (loop_observers next counter reversed state depth).2)

end Blotto.BinarySeedTraceBounds
