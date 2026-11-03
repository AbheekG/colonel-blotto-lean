import Blotto.PlayerSpecificFiniteParameterCost
import Blotto.BinaryFrameEncodingCost

/-! Actual portable binary descriptions for copied rational/natural record
words. Existing self-delimiting rational/natural frames supply a decoder
that round-trips every original record word and preserves a trailing suffix.
Arithmetic/comparison events cannot occur in a certified copy-only frame. -/
namespace Blotto.PlayerSpecificCopyFrame
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def PureEvent : Event → Prop | .copy _ | .control _ => True | _ => False
def Pure (trace : Trace) : Prop := ∀ e∈trace,PureEvent e
def one : Event → List Bool
  | .copy q => false::BinaryRatFrame.encode q
  | .control n => true::BinaryNatFrame.encode n
  | _ => []
def payload (trace : Trace) : List Bool := trace.flatMap one
def encode (trace : Trace) : List Bool := BinaryNatFrame.encode trace.length++payload trace
def readOne : List Bool → Option (Event×List Bool)
  | [] => none
  | false::bits => (BinaryRatFrame.read bits).map (fun parsed => (.copy parsed.1,parsed.2))
  | true::bits => (BinaryNatFrame.read bits).map (fun parsed => (.control parsed.1,parsed.2))
def readMany : ℕ → List Bool → Option (Trace×List Bool)
  | 0,bits => some ([],bits)
  | k+1,bits => (readOne bits).bind (fun first =>
      (readMany k first.2).map (fun rest => (first.1::rest.1,rest.2)))
def read (bits : List Bool) : Option (Trace×List Bool) :=
  (BinaryNatFrame.read bits).bind (fun header => readMany header.1 header.2)

theorem pure_append (a b : Trace) : Pure (a++b) ↔ Pure a ∧ Pure b := by
  simp only [Pure,List.mem_append,or_imp,forall_and]
theorem pure_copyRow (row : List ℚ) : Pure (copyRow row) := by
  intro e he
  rcases List.mem_cons.mp he with he|he
  · subst e; trivial
  · obtain ⟨q,_,rfl⟩:=List.mem_map.mp he
    trivial
theorem pure_controls (words : List ℕ) : Pure (words.map Event.control) := by
  intro e he
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp he
  trivial
theorem head_pure (e : Event) (trace : Trace) (h : Pure (e::trace)) : PureEvent e := h e List.mem_cons_self
theorem tail_pure (e : Event) (trace : Trace) (h : Pure (e::trace)) : Pure trace :=
  fun x hx => h x (List.mem_cons_of_mem e hx)

theorem read_one (e : Event) (h : PureEvent e) (suffix : List Bool) : readOne (one e++suffix)=some (e,suffix) := by
  cases e with
  | copy q => simp only [one,List.cons_append,readOne,BinaryRatFrame.read_encode_append,Option.map_some]
  | control n => simp only [one,List.cons_append,readOne,BinaryNatFrame.read_encode_append,Option.map_some]
  | arithmetic op a b => cases h
  | compare a b => cases h

theorem read_payload (trace : Trace) (h : Pure trace) (suffix : List Bool) :
    readMany trace.length (payload trace++suffix)=some (trace,suffix) := by
  induction trace with
  | nil => rfl
  | cons e trace ih =>
    simp only [List.length_cons,payload,List.flatMap_cons,List.append_assoc,readMany,
      read_one e (head_pure e trace h),Option.bind_some]
    rw [show trace.flatMap one=payload trace from rfl,ih (tail_pure e trace h),Option.map_some]

theorem read_encode (trace : Trace) (h : Pure trace) (suffix : List Bool) :
    read (encode trace++suffix)=some (trace,suffix) := by
  simp only [encode,List.append_assoc,read,BinaryNatFrame.read_encode_append,Option.bind_some]
  exact read_payload trace h suffix

theorem one_length (e : Event) (h : PureEvent e) : (one e).length=2*e.price RationalCostModel.schoolbook := by
  cases e with
  | copy q => simp only [one,List.length_cons,BinaryRatFrame.encode_length,Event.price]; omega
  | control n => simp only [one,List.length_cons,BinaryNatFrame.encode_length,Event.price]; omega
  | arithmetic op a b => cases h
  | compare a b => cases h

theorem payload_length (trace : Trace) (h : Pure trace) : (payload trace).length=2*price RationalCostModel.schoolbook trace := by
  induction trace with
  | nil => rfl
  | cons e trace ih =>
    simp only [payload,List.flatMap_cons,List.length_append,one_length e (head_pure e trace h)]
    rw [show trace.flatMap one=payload trace from rfl,ih (tail_pure e trace h)]
    simp only [price,List.map_cons,List.sum_cons]
    omega

theorem length_le_price (trace : Trace) (h : Pure trace) : trace.length≤price RationalCostModel.schoolbook trace := by
  induction trace with
  | nil => rfl
  | cons e trace ih =>
    have he : 1≤e.price RationalCostModel.schoolbook := by
      cases e with
      | copy q => simp only [Event.price]; omega
      | control n => simp only [Event.price]; omega
      | compare a b => simp only [Event.price]; omega
      | arithmetic op a b => cases op <;> simp only [Event.price] <;> omega
    have ht:=ih (tail_pure e trace h)
    simp only [List.length_cons,price,List.map_cons,List.sum_cons]
    change trace.length≤(trace.map (Event.price RationalCostModel.schoolbook)).sum at ht
    omega

theorem encoded_length (trace : Trace) (h : Pure trace) :
    (encode trace).length≤4*price RationalCostModel.schoolbook trace+3 := by
  have hn:=length_le_price trace h
  have hw:=PlayerSpecificRationalTrace.control_width trace.length
  rw [encode,List.length_append,BinaryNatFrame.encode_length,payload_length trace h]
  omega

end Blotto.PlayerSpecificCopyFrame
