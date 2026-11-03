import Blotto.BinarySeedCursorWork
import Blotto.BinaryTraceDepth

/-! One structural cursor execution returns its data, old allocation trace
and source-work counter together. Work/visit/trace fields are ghost observers;
their native evaluation is outside the Boolean/list source-work model. -/

namespace Blotto.BinarySeedCursorMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTraceDepth
set_option autoImplicit false

def reverseAt (bits acc : List Bool) (depth : ℕ) : (List Bool × Trace) × ℕ :=
  match bits with
  | [] => ((acc,[.frames (depth+1)]),2)
  | bit::rest =>
      let later := reverseAt rest (bit::acc) (depth+1)
      ((later.1.1,.frames (depth+1)::.listAllocation 1::later.1.2),later.2+4)

theorem reverseAt_erases (bits acc : List Bool) (depth : ℕ) :
    (reverseAt bits acc depth).1 =
      ((reverseWithTrace bits acc).1,under depth (reverseWithTrace bits acc).2) := by
  induction bits generalizing acc depth with
  | nil => rfl
  | cons bit rest ih =>
      simp only [reverseAt,reverseWithTrace,ih,under_append,under_compose]
      rfl

def reverse (bits acc : List Bool) : (List Bool × Trace) × ℕ := reverseAt bits acc 0

theorem reverse_erases (bits acc : List Bool) :
    (reverse bits acc).1 = reverseWithTrace bits acc := by
  rw [reverse,reverseAt_erases,under_zero]

theorem reverseAt_work (bits acc : List Bool) (depth : ℕ) :
    (reverseAt bits acc depth).2 = (BinaryMidpointTapeLifetime.reverseWithWork bits acc).2 := by
  induction bits generalizing acc depth with
  | nil => rfl
  | cons bit rest ih => simp only [reverseAt,BinaryMidpointTapeLifetime.reverseWithWork,ih]

theorem reverse_work (bits acc : List Bool) :
    (reverse bits acc).2 = (BinaryMidpointTapeLifetime.reverseWithWork bits acc).2 := by
  exact reverseAt_work bits acc 0

theorem reverseAt_trace_length (bits acc : List Bool) (depth : ℕ) :
    (reverseAt bits acc depth).1.2.length = 2*bits.length+1 := by
  induction bits generalizing acc depth with
  | nil => rfl
  | cons bit rest ih => simp only [reverseAt,List.length_cons,ih]; omega

theorem reverseAt_frames (bits acc : List Bool) (depth : ℕ) :
    framePeak (reverseAt bits acc depth).1.2 ≤ depth+bits.length+1 := by
  induction bits generalizing acc depth with
  | nil => simp [reverseAt,framePeak]
  | cons bit rest ih =>
      have h := ih (bit::acc) (depth+1)
      simp only [reverseAt,framePeak,List.length_cons] at h ⊢
      omega

structure Cursor where
  data : Option (List Bool × List Bool)
  trace : Trace
  work : ℕ
  visits : ℕ

def loopAt : List Bool → List Bool → List Bool → ℕ → Cursor
  | [],bits,reversed,depth =>
      let back := reverseAt reversed [] (depth+1)
      ⟨some (back.1.1,bits),.frames (depth+1)::back.1.2,back.2+2,1⟩
  | _::_,[],_,depth => ⟨none,[.frames (depth+1)],2,1⟩
  | _::ruler,bit::bits,reversed,depth =>
      let later := loopAt ruler bits (bit::reversed) (depth+1)
      ⟨later.data,.frames (depth+1)::.listAllocation 1::later.trace,
        later.work+4,later.visits+1⟩

theorem loopAt_erases (ruler bits reversed : List Bool) (depth : ℕ) :
    ((loopAt ruler bits reversed depth).data,(loopAt ruler bits reversed depth).trace) =
      ((cursorWithTrace ruler bits reversed).1,under depth (cursorWithTrace ruler bits reversed).2) := by
  induction ruler generalizing bits reversed depth with
  | nil =>
      simp only [loopAt,cursorWithTrace,reverseAt_erases,under_append,under_compose]
      rfl
  | cons cell ruler ih => cases bits with
    | nil => rfl
    | cons bit bits =>
        have h := ih bits (bit::reversed) (depth+1)
        have hd := congrArg Prod.fst h
        have ht := congrArg Prod.snd h
        dsimp only at hd ht
        simp only [loopAt,cursorWithTrace,hd,ht,under_append,under_compose]
        rfl

def loop (ruler bits reversed : List Bool) : Cursor := loopAt ruler bits reversed 0

theorem loop_erases (ruler bits reversed : List Bool) :
    ((loop ruler bits reversed).data,(loop ruler bits reversed).trace) =
      cursorWithTrace ruler bits reversed := by
  simpa only [loop,under_zero] using loopAt_erases ruler bits reversed 0

theorem loopAt_work (ruler bits reversed : List Bool) (depth : ℕ) :
    (loopAt ruler bits reversed depth).work =
      (BinarySeedCursorWork.loopWithWork ruler bits reversed).2 := by
  induction ruler generalizing bits reversed depth with
  | nil => simp only [loopAt,BinarySeedCursorWork.loopWithWork,reverseAt_work]
  | cons cell ruler ih => cases bits with
    | nil => rfl
    | cons bit bits => exact congrArg (·+4) (ih bits (bit::reversed) (depth+1))

theorem loop_work (ruler bits reversed : List Bool) :
    (loop ruler bits reversed).work =
      (BinarySeedCursorWork.loopWithWork ruler bits reversed).2 := by
  exact loopAt_work ruler bits reversed 0

theorem loopAt_visits (ruler bits reversed : List Bool) (depth : ℕ) :
    (loopAt ruler bits reversed depth).visits = BinarySeedCursor.visits ruler bits := by
  induction ruler generalizing bits reversed depth with
  | nil => rfl
  | cons cell ruler ih => cases bits with
    | nil => rfl
    | cons bit bits => exact congrArg (·+1) (ih bits (bit::reversed) (depth+1))

theorem loop_visits (ruler bits reversed : List Bool) :
    (loop ruler bits reversed).visits = BinarySeedCursor.visits ruler bits := by
  exact loopAt_visits ruler bits reversed 0

theorem loopAt_trace_length (ruler bits reversed : List Bool) (depth : ℕ) :
    (loopAt ruler bits reversed depth).trace.length ≤ 4*ruler.length+2*reversed.length+2 := by
  induction ruler generalizing bits reversed depth with
  | nil => simp only [loopAt,List.length_cons,reverseAt_trace_length,List.length_nil]; omega
  | cons cell ruler ih => cases bits with
    | nil => simp only [loopAt,List.length_cons,List.length_nil]; omega
    | cons bit bits =>
        have h := ih bits (bit::reversed) (depth+1)
        simp only [loopAt,List.length_cons] at h ⊢
        omega

theorem loopAt_frames (ruler bits reversed : List Bool) (depth : ℕ) :
    framePeak (loopAt ruler bits reversed depth).trace ≤
      depth+2*ruler.length+reversed.length+2 := by
  induction ruler generalizing bits reversed depth with
  | nil =>
      have h := reverseAt_frames reversed [] (depth+1)
      simp only [loopAt,framePeak,List.length_nil] at h ⊢
      omega
  | cons cell ruler ih => cases bits with
    | nil => simp only [loopAt,framePeak,List.length_cons]; omega
    | cons bit bits =>
        have h := ih bits (bit::reversed) (depth+1)
        simp only [loopAt,framePeak,List.length_cons] at h ⊢
        omega

def consume (ruler bits : List Bool) : (Option (List Bool × List Bool) × Trace) × ℕ :=
  let result := loop ruler bits []
  ((result.data,result.trace++[.frames result.visits]),result.work)

theorem consume_erases (ruler bits : List Bool) :
    (consume ruler bits).1 =
      ((consumeWithTrace ruler bits).1.1,(consumeWithTrace ruler bits).2) := by
  have h := loop_erases ruler bits []
  unfold consume
  dsimp only
  rw [loop_visits]
  exact congrArg (fun d => (d.1,d.2++[.frames (BinarySeedCursor.visits ruler bits)])) h

theorem consume_data (ruler bits : List Bool) :
    (consume ruler bits).1.1 = (consumeWithTrace ruler bits).1.1 := by
  have h := congrArg (fun d : Option (List Bool × List Bool) × Trace => d.1)
    (consume_erases ruler bits)
  exact h

theorem consume_trace (ruler bits : List Bool) :
    (consume ruler bits).1.2 = (consumeWithTrace ruler bits).2 :=
  congrArg (fun d : Option (List Bool × List Bool) × Trace => d.2) (consume_erases ruler bits)

theorem consume_work (ruler bits : List Bool) :
    (consume ruler bits).2 = (BinarySeedCursorWork.consumeWithWork ruler bits).2 :=
  loop_work ruler bits []

theorem consume_bound (ruler bits : List Bool) :
    (consume ruler bits).2 ≤ 8*ruler.length+4 := by
  rw [consume_work]
  exact BinarySeedCursorWork.consume_work ruler bits

end Blotto.BinarySeedCursorMeasured
