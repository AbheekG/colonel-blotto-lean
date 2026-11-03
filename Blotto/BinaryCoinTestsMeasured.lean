import Blotto.BinaryWordCoinPrimitivesMeasured

/-! Coin tests return their actual answer, visit count and one-cell-per-visit
ruler. A linear depth-indexed emitter reproduces the old test traces without
repeated under/append traversals. Source charges count the explicit scans and
emission; native Nat arithmetic, record/reference layout and GC remain separate.
The actual data-only scan/emitter do not execute their charge observers. -/
namespace Blotto.BinaryCoinTestsMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Scan where
  answer : Bool
  visits : ℕ
  ruler : List Bool

def zero : List Bool → Scan
  | [] => ⟨true,1,[false]⟩
  | true::_ => ⟨false,1,[false]⟩
  | false::rest =>
      let later := zero rest
      ⟨later.answer,later.visits+1,false::later.ruler⟩

def same : List Bool → List Bool → Scan
  | [],[] => ⟨true,1,[false]⟩
  | a::rest,b::tail =>
      if a=b then
        let later := same rest tail
        ⟨later.answer,later.visits+1,false::later.ruler⟩
      else ⟨false,1,[false]⟩
  | _,_ => ⟨false,1,[false]⟩

theorem zero_visits (bits : List Bool) : (zero bits).visits = FixedBinaryWord.zeroVisits bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [zero,FixedBinaryWord.zeroVisits,
      Bool.false_eq_true,ite_false,ite_true,ih,Nat.add_comm]

theorem same_visits (first second : List Bool) :
    (same first second).visits = FixedBinaryWord.sameVisits first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail =>
        simp only [same,FixedBinaryWord.sameVisits]
        split <;> simp only [ih] <;> omega

theorem zero_ruler (bits : List Bool) : (zero bits).ruler.length = (zero bits).visits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [zero,List.length_cons,List.length_nil,ih]

theorem same_ruler (first second : List Bool) : (same first second).ruler.length = (same first second).visits := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail =>
        simp only [same]
        split <;> simp only [List.length_cons,List.length_nil,ih]

theorem zero_bound (bits : List Bool) : 1 ≤ (zero bits).visits ∧ (zero bits).visits ≤ bits.length+1 := by
  constructor
  · cases bits with
    | nil => rfl
    | cons bit rest => cases bit <;> simp [zero]
  · rw [zero_visits]; exact FixedBinaryWord.zeroVisits_bound bits

theorem same_bound (first second : List Bool) :
    1 ≤ (same first second).visits ∧ (same first second).visits ≤ first.length+1 := by
  constructor
  · cases first with
    | nil => cases second <;> simp [same]
    | cons bit rest => cases second with
      | nil => simp [same]
      | cons other tail => simp only [same]; split <;> simp
  · rw [same_visits]; exact FixedBinaryWord.sameVisits_bound first second

def charge (width : ℕ) (zeroScan sameScan : Scan) : ℕ :=
  3*zeroScan.visits+4*sameScan.visits+17*width+22

theorem charge_eq {w : ℕ} (a b : FixedBinaryWord w) :
    charge w (zero a.bits) (same a.bits b.bits) =
      3*FixedBinaryWord.zeroVisits a.bits+4*FixedBinaryWord.sameVisits a.bits b.bits+17*a.bits.length+22 := by
  simp only [charge,zero_visits,same_visits,a.size]

theorem charge_bound {w : ℕ} (a b : FixedBinaryWord w) :
    charge w (zero a.bits) (same a.bits b.bits) ≤ 32*(w+1) := by
  have hz := (zero_bound a.bits).2
  have hs := (same_bound a.bits b.bits).2
  have ha := a.size
  unfold charge
  omega

theorem charge_width {w : ℕ} (a b : FixedBinaryWord w) :
    binaryWordWidth (charge w (zero a.bits) (same a.bits b.bits)) ≤ binaryWordWidth (32*(w+1)) :=
  binaryWordWidth_mono (charge_bound a b)

def events : List Bool → ℕ → Trace
  | [],_depth => []
  | _::rest,depth =>
      let next := depth+1
      .frames next :: .arrayAllocation 4 :: events rest next

theorem events_shift (ruler : List Bool) (depth : ℕ) :
    events ruler (depth+1) = under 1 (events ruler depth) := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih =>
      simp only [events,under,List.map_cons,shiftEvent]
      rw [ih]
      simp only [under]
      congr 2 <;> omega

theorem events_length (ruler : List Bool) (depth : ℕ) : (events ruler depth).length = 2*ruler.length := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [events,List.length_cons,ih]; omega

theorem events_frames (ruler : List Bool) (depth : ℕ) : framePeak (events ruler depth) ≤ depth+ruler.length := by
  induction ruler generalizing depth with
  | nil => simp [events,framePeak]
  | cons bit rest ih =>
      have h := ih (depth+1)
      simp only [events,framePeak,List.length_cons]
      omega

theorem events_arrays (ruler : List Bool) (depth : ℕ) : arraySlots (events ruler depth) = 4*ruler.length := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [events,arraySlots,ih,List.length_cons]; omega

theorem events_lists (ruler : List Bool) (depth : ℕ) : listCells (events ruler depth) = 0 := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [events,listCells,ih]

theorem frame_member_le (trace : Trace) (count : ℕ) (h : .frames count ∈ trace) : count ≤ framePeak trace := by
  induction trace with
  | nil => simp at h
  | cons event rest ih =>
      rcases List.mem_cons.mp h with he | ht
      · subst event; simp [framePeak]
      · have hh := ih ht
        cases event <;> simp only [framePeak] <;> omega

theorem event_frame_bound (ruler : List Bool) (depth count : ℕ) (h : .frames count ∈ events ruler depth) :
    count ≤ depth+ruler.length := (frame_member_le _ _ h).trans (events_frames ruler depth)

theorem event_frame_width (ruler : List Bool) (depth count : ℕ) (h : .frames count ∈ events ruler depth) :
    binaryWordWidth count ≤ binaryWordWidth (depth+ruler.length) :=
  binaryWordWidth_mono (event_frame_bound ruler depth count h)

def emit (scanned : Scan) : Bool × Trace := (scanned.answer,events scanned.ruler 0)

theorem zero_compat (bits : List Bool) : emit (zero bits) = (BinaryWordCoinPrimitivesMeasured.zero bits).1 := by
  rw [BinaryWordCoinPrimitivesMeasured.zero_erases]
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit with
    | true => rfl
    | false =>
        simp only [emit,zero,BinaryWordCoinLifetime.zeroWithTrace,
          BinaryBooleanPrimitiveLifetime.scanWithTrace,Bool.false_eq_true,ite_false,events]
        have hd := congrArg Prod.fst ih
        have ht := congrArg Prod.snd ih
        simp only [emit] at hd ht
        rw [events_shift,ht]
        exact congrArg (fun b => (b,_)) hd

theorem same_compat (first second : List Bool) :
    emit (same first second) = (BinaryWordCoinPrimitivesMeasured.same first second).1 := by
  rw [BinaryWordCoinPrimitivesMeasured.same_erases]
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail =>
        simp only [same,BinaryWordCoinLifetime.sameWithTrace]
        split
        · have h := ih tail
          have hd := congrArg Prod.fst h
          have ht := congrArg Prod.snd h
          simp only [emit] at hd ht ⊢
          simp only [events]
          rw [events_shift,ht]
          exact congrArg (fun b => (b,_)) hd
        · rfl

-- Explicit source operations for the actual scan and emitter recursions.
-- Nat increments are labels here; their bit-width/representation join is open.
def zeroCharged : List Bool → Scan × ℕ
  | [] => (⟨true,1,[false]⟩,6)
  | true::_ => (⟨false,1,[false]⟩,6)
  | false::rest =>
      let later := zeroCharged rest
      (⟨later.1.answer,later.1.visits+1,false::later.1.ruler⟩,later.2+6)

def sameCharged : List Bool → List Bool → Scan × ℕ
  | [],[] => (⟨true,1,[false]⟩,6)
  | a::rest,b::tail =>
      if a=b then
        let later := sameCharged rest tail
        (⟨later.1.answer,later.1.visits+1,false::later.1.ruler⟩,later.2+6)
      else (⟨false,1,[false]⟩,6)
  | _,_ => (⟨false,1,[false]⟩,6)

def eventsCharged : List Bool → ℕ → Trace × ℕ
  | [],_depth => ([],2)
  | _::rest,depth =>
      let next := depth+1
      let later := eventsCharged rest next
      (.frames next :: .arrayAllocation 4 :: later.1,later.2+6)

theorem zeroCharged_erases (bits : List Bool) : (zeroCharged bits).1 = zero bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [zeroCharged,zero,ih]

theorem sameCharged_erases (first second : List Bool) : (sameCharged first second).1 = same first second := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail => simp only [sameCharged,same,ih]; split <;> rfl

theorem eventsCharged_erases (ruler : List Bool) (depth : ℕ) : (eventsCharged ruler depth).1 = events ruler depth := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [eventsCharged,events,ih]

theorem zeroCharged_work (bits : List Bool) : (zeroCharged bits).2 = 6*(zero bits).visits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [zeroCharged,zero,ih]; omega

theorem sameCharged_work (first second : List Bool) :
    (sameCharged first second).2 = 6*(same first second).visits := by
  induction first generalizing second with
  | nil => cases second <;> rfl
  | cons bit rest ih => cases second with
    | nil => rfl
    | cons other tail => simp only [sameCharged,same,ih]; split <;> dsimp only <;> omega

theorem eventsCharged_work (ruler : List Bool) (depth : ℕ) :
    (eventsCharged ruler depth).2 = 6*ruler.length+2 := by
  induction ruler generalizing depth with
  | nil => rfl
  | cons bit rest ih => simp only [eventsCharged,ih,List.length_cons]; omega

theorem tests_work_bound (first second : List Bool) :
    (zeroCharged first).2+(sameCharged first second).2+
      (eventsCharged (zero first).ruler 0).2+(eventsCharged (same first second).ruler 0).2 ≤
      24*(first.length+1)+4 := by
  have hz := zero_bound first
  have hs := same_bound first second
  rw [zeroCharged_work,sameCharged_work,eventsCharged_work,eventsCharged_work,zero_ruler,same_ruler]
  omega

theorem tests_work_le_charge {w : ℕ} (a b : FixedBinaryWord w) :
    (zeroCharged a.bits).2+(sameCharged a.bits b.bits).2+
      (eventsCharged (zero a.bits).ruler 0).2+(eventsCharged (same a.bits b.bits).ruler 0).2 ≤
      2*charge w (zero a.bits) (same a.bits b.bits) := by
  have h := tests_work_bound a.bits b.bits
  have ha := a.size
  unfold charge
  omega

theorem test_scalar_widths {w : ℕ} (a b : FixedBinaryWord w) :
    binaryWordWidth (zero a.bits).visits ≤ binaryWordWidth (w+1) ∧
      binaryWordWidth (same a.bits b.bits).visits ≤ binaryWordWidth (w+1) := by
  have hz := (zero_bound a.bits).2
  have hs := (same_bound a.bits b.bits).2
  rw [a.size] at hz hs
  exact ⟨binaryWordWidth_mono hz,binaryWordWidth_mono hs⟩

theorem tests_trace_cells (first second : List Bool) :
    (emit (zero first)).2.length+(emit (same first second)).2.length ≤ 4*(first.length+1) := by
  have hz := zero_bound first
  have hs := same_bound first second
  simp only [emit,events_length,zero_ruler,same_ruler]
  omega

theorem tests_ruler_cells (first second : List Bool) :
    (zero first).ruler.length+(same first second).ruler.length ≤ 2*(first.length+1) := by
  rw [zero_ruler,same_ruler]
  have hz := zero_bound first
  have hs := same_bound first second
  omega

end Blotto.BinaryCoinTestsMeasured
