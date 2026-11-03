import Blotto.PlayerSpecificCopyFrame

/-! Actual framed description encoding has polynomial source bit work,
including natural/rational payload generation, every accumulated-buffer
copy, header, traversal and final emitted bits. -/
namespace Blotto.PlayerSpecificCopyFrameCost
open PlayerSpecificRationalTrace PlayerSpecificCopyFrame
set_option autoImplicit false
set_option maxHeartbeats 2500000

def oneWork : Event → ℕ
  | .copy q => BinaryRatFrame.encodingBitWork (fun w => w) q+(one (.copy q)).length+8
  | .control n => BinaryNatFrame.encodingBitWork (fun w => w) n+(one (.control n)).length+8
  | _ => 0
def concatWork : Trace → ℕ → ℕ
  | [],accumulated => accumulated
  | e::rest,accumulated =>
    let next:=accumulated+(one e).length
    next+concatWork rest next
def work (trace : Trace) : ℕ :=
  BinaryNatFrame.encodingBitWork (fun w => w) trace.length+(trace.map oneWork).sum+
    concatWork trace 0+trace.length+(BinaryNatFrame.encode trace.length).length+(payload trace).length

theorem one_work (e : Event) (h : PureEvent e) (B : ℕ) (hB : e.price RationalCostModel.schoolbook≤B) :
    oneWork e≤100*(B+1)^2 := by
  have hlen:=one_length e h
  cases e with
  | copy q =>
    have hw : rationalWordWidth q≤B := by change 1+rationalWordWidth q≤B at hB; omega
    have hp:=BinaryRatFrame.encodingBitWork_uniform_bound (fun w => w) 1 (by intro w; omega) q B hw
    simp only [oneWork]
    nlinarith only [hp,hlen,hB]
  | control n =>
    have hw : binaryWordWidth n≤B := by change 1+binaryWordWidth n≤B at hB; omega
    have hp:=BinaryNatFrame.encodingBitWork_uniform_bound (fun w => w) 1 (by intro w; omega) n B hw
    simp only [oneWork]
    nlinarith only [hp,hlen,hB]
  | arithmetic op a b => cases h
  | compare a b => cases h

theorem member_price (trace : Trace) (e : Event) (he : e∈trace) : e.price RationalCostModel.schoolbook≤price RationalCostModel.schoolbook trace := by
  induction trace with
  | nil => cases he
  | cons first rest ih =>
    simp only [price,List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp he with he|ht
    · subst e; omega
    · have hh:=ih ht
      change e.price RationalCostModel.schoolbook≤(rest.map (Event.price RationalCostModel.schoolbook)).sum at hh
      omega

theorem sum_work (trace : Trace) (h : Pure trace) (B : ℕ)
    (hB : ∀ e∈trace,e.price RationalCostModel.schoolbook≤B) :
    (trace.map oneWork).sum≤trace.length*(100*(B+1)^2) := by
  induction trace with
  | nil => simp
  | cons e trace ih =>
    have he:=one_work e (head_pure e trace h) B (hB e List.mem_cons_self)
    have ht:=ih (tail_pure e trace h) (fun x hx => hB x (List.mem_cons_of_mem e hx))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [he,ht]

theorem concat_bound (trace : Trace) (accumulated : ℕ) :
    concatWork trace accumulated≤(trace.length+1)*(accumulated+(payload trace).length) := by
  induction trace generalizing accumulated with
  | nil => simp only [concatWork,payload,List.flatMap_nil,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.one_mul,Nat.le_refl]
  | cons e trace ih =>
    have ht:=ih (accumulated+(one e).length)
    simp only [concatWork,payload,List.flatMap_cons,List.length_append,List.length_cons] at ht ⊢
    nlinarith only [ht]

theorem source_work (trace : Trace) (h : Pure trace) :
    work trace≤1000*(price RationalCostModel.schoolbook trace+2)^3 := by
  let B:=price RationalCostModel.schoolbook trace
  have hn:=length_le_price trace h
  have hw:=PlayerSpecificRationalTrace.control_width trace.length
  have hsum:=sum_work trace h B (fun e he => member_price trace e he)
  have hsump:=Nat.mul_le_mul_right (100*(B+1)^2) hn
  have hconcat:=concat_bound trace 0
  rw [payload_length trace h] at hconcat
  have hheader:=BinaryNatFrame.encodingBitWork_uniform_bound (fun w => w) 1 (by intro w; omega)
    trace.length (B+1) (by omega)
  have hlength:=BinaryNatFrame.encode_length trace.length
  unfold work
  rw [payload_length trace h]
  have hB2 : 0≤B^2 := Nat.zero_le _
  have hB3 : 0≤B^3 := Nat.zero_le _
  nlinarith only [hn,hw,hsum,hsump,hconcat,hheader,hlength,hB2,hB3]

end Blotto.PlayerSpecificCopyFrameCost
