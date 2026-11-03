import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryWordWidthCore
import Blotto.BinaryTraceDepth

/-! A concrete trace plan delays concatenation until one structural emission.
Blocks are borrowed trace lists; joins retain two child references. Emission
copies each block once into its supplied suffix, without append or reverse.
A shifted block applies shiftEvent once per reached event; emitFull forwards
that actual primitive count separately from its list/control charge. Work counts named list/control operations. Native scalar,
record/reference layout, stack and allocator interpretation remain separate. -/
namespace Blotto.BinaryTracePlanMeasured
open BinarySeedPreparationSpace
set_option autoImplicit false

inductive Plan where
  | block (events : Trace)
  | join (first second : Plan)
  | shifted (depth : ℕ) (events : Trace)

def denote : Plan → Trace
  | .block events => events
  | .join first second => denote first ++ denote second
  | .shifted depth events => under depth events

def payload : Plan → ℕ
  | .block events => events.length
  | .join first second => payload first + payload second
  | .shifted _ events => events.length

def nodes : Plan → ℕ
  | .block _ => 1
  | .join first second => nodes first + nodes second + 1
  | .shifted _ _ => 1

theorem nodes_pos (plan : Plan) : 0 < nodes plan := by
  cases plan <;> simp [nodes] <;> omega

theorem denote_length (plan : Plan) : (denote plan).length = payload plan := by
  induction plan with
  | block events => rfl
  | join first second ihFirst ihSecond => simp only [denote,payload,List.length_append,ihFirst,ihSecond]
  | shifted depth events => simp [denote,payload,under]

def prepend : Trace → Trace → Trace × ℕ
  | [],suffix => (suffix,2)
  | event::rest,suffix =>
      let later := prepend rest suffix
      (event::later.1,later.2+4)

theorem prepend_data (events suffix : Trace) : (prepend events suffix).1 = events++suffix := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prepend,List.cons_append,ih]

theorem prepend_work (events suffix : Trace) : (prepend events suffix).2 = 4*events.length+2 := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prepend,List.length_cons,ih]; omega

-- The first charge is the same list/control profile as prepend. The second
-- counts reached shiftEvent primitives, whose native scalar price is separate.
def prependShifted (depth : ℕ) : Trace → Trace → (Trace × ℕ) × ℕ
  | [],suffix => ((suffix,2),0)
  | event::rest,suffix =>
      let later := prependShifted depth rest suffix
      (((shiftEvent depth event)::later.1.1,later.1.2+4),later.2+1)

theorem prependShifted_data (depth : ℕ) (events suffix : Trace) :
    (prependShifted depth events suffix).1.1 = under depth events++suffix := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prependShifted,under,List.map_cons,List.cons_append,ih]

theorem prependShifted_work (depth : ℕ) (events suffix : Trace) :
    (prependShifted depth events suffix).1.2 = 4*events.length+2 := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prependShifted,List.length_cons,ih]; omega

theorem prependShifted_shifts (depth : ℕ) (events suffix : Trace) :
    (prependShifted depth events suffix).2 = events.length := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prependShifted,List.length_cons,ih]

def emit : Plan → Trace → Trace × ℕ
  | .block events,suffix => prepend events suffix
  | .join first second,suffix =>
      let right := emit second suffix
      let left := emit first right.1
      (left.1,left.2+right.2+2)
  | .shifted depth events,suffix => (prependShifted depth events suffix).1

theorem emit_data (plan : Plan) (suffix : Trace) :
    (emit plan suffix).1 = denote plan++suffix := by
  induction plan generalizing suffix with
  | block events => exact prepend_data events suffix
  | join first second ihFirst ihSecond =>
      simp only [emit,denote,ihFirst,ihSecond,List.append_assoc]
  | shifted depth events => exact prependShifted_data depth events suffix

theorem emit_work (plan : Plan) (suffix : Trace) :
    (emit plan suffix).2 = 4*payload plan+2*nodes plan := by
  induction plan generalizing suffix with
  | block events => exact prepend_work events suffix
  | join first second ihFirst ihSecond =>
      simp only [emit,payload,nodes,ihFirst,ihSecond]
      omega
  | shifted depth events => exact prependShifted_work depth events suffix

def shiftCount : Plan → ℕ
  | .block _ => 0
  | .join first second => shiftCount first+shiftCount second
  | .shifted _ events => events.length

theorem shiftCount_bound (plan : Plan) : shiftCount plan ≤ payload plan := by
  induction plan with
  | block events => simp [shiftCount]
  | join first second ihFirst ihSecond => simp only [shiftCount,payload]; omega
  | shifted depth events => rfl

def emitFull : Plan → Trace → (Trace × ℕ) × ℕ
  | .block events,suffix => (prepend events suffix,0)
  | .join first second,suffix =>
      let right := emitFull second suffix
      let left := emitFull first right.1.1
      ((left.1.1,left.1.2+right.1.2+2),left.2+right.2)
  | .shifted depth events,suffix => prependShifted depth events suffix

theorem emitFull_erases (plan : Plan) (suffix : Trace) : (emitFull plan suffix).1 = emit plan suffix := by
  induction plan generalizing suffix with
  | block events => rfl
  | join first second ihFirst ihSecond => simp only [emitFull,emit,ihFirst,ihSecond]
  | shifted depth events => rfl

theorem emitFull_shifts (plan : Plan) (suffix : Trace) : (emitFull plan suffix).2 = shiftCount plan := by
  induction plan generalizing suffix with
  | block events => rfl
  | join first second ihFirst ihSecond => simp only [emitFull,shiftCount,ihFirst,ihSecond]
  | shifted depth events => exact prependShifted_shifts depth events suffix

theorem emitFull_total (plan : Plan) (suffix : Trace) (B : ℕ)
    (h : payload plan+nodes plan ≤ B) :
    (emitFull plan suffix).1.2+(emitFull plan suffix).2 ≤ 5*B := by
  rw [emitFull_erases,emit_work,emitFull_shifts]
  have hs := shiftCount_bound plan
  omega

theorem emit_length (plan : Plan) (suffix : Trace) :
    (emit plan suffix).1.length = payload plan+suffix.length := by
  rw [emit_data,List.length_append,denote_length]

theorem emit_work_bound (plan : Plan) (suffix : Trace) (B : ℕ)
    (h : payload plan+nodes plan ≤ B) : (emit plan suffix).2 ≤ 4*B := by
  rw [emit_work]
  omega

theorem emit_work_width (plan : Plan) (suffix : Trace) (B : ℕ)
    (h : payload plan+nodes plan ≤ B) :
    binaryWordWidth (emit plan suffix).2 ≤ binaryWordWidth (4*B) :=
  binaryWordWidth_mono (emit_work_bound plan suffix B h)

-- Logical source activations, not bytes of compiled stack. These observers
-- follow the actual right-before-left emitter and the reached prepend loop.
def prependFrames : Trace → ℕ
  | [] => 1
  | _::rest => prependFrames rest+1

theorem prependFrames_eq (events : Trace) : prependFrames events = events.length+1 := by
  induction events with
  | nil => rfl
  | cons event rest ih => simp only [prependFrames,List.length_cons,ih]

def emitFrames : Plan → ℕ
  | .block events => prependFrames events+1
  | .join first second => max (emitFrames first) (emitFrames second)+1
  | .shifted _ events => prependFrames events+1

theorem emitFrames_bound (plan : Plan) : emitFrames plan ≤ payload plan+nodes plan+1 := by
  induction plan with
  | block events => simp only [emitFrames,prependFrames_eq,payload,nodes]; omega
  | join first second ihFirst ihSecond => simp only [emitFrames,payload,nodes]; omega
  | shifted depth events => simp only [emitFrames,prependFrames_eq,payload,nodes]; omega

theorem emitFrames_width (plan : Plan) (B : ℕ) (h : payload plan+nodes plan ≤ B) :
    binaryWordWidth (emitFrames plan) ≤ binaryWordWidth (B+1) :=
  binaryWordWidth_mono ((emitFrames_bound plan).trans (by omega))

-- A block stores one trace reference, a join two plan references. Event
-- payloads are borrowed during emission; exactly payload plan new list cells
-- are consed. Plan headers and emit-result records have fixed source arity.
def planReferences : Plan → ℕ
  | .block _ => 1
  | .join first second => planReferences first+planReferences second+2
  | .shifted _ _ => 2

theorem planReferences_bound (plan : Plan) : planReferences plan ≤ 2*nodes plan := by
  induction plan with
  | block events => simp [planReferences,nodes]
  | join first second ihFirst ihSecond => simp only [planReferences,nodes]; omega
  | shifted depth events => rfl

end Blotto.BinaryTracePlanMeasured
