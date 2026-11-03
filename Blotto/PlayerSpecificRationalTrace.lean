import Blotto.PlayerSpecificSturmHeights

/-! Operand-sized source prices for the polynomial backend. Numerical
operations record their actual operands and returned value. Copies and
integer control words are included; no aggregate cost/width oracle is an
input. Prices use the paper's existing rational-primitive majorant. -/
namespace Blotto.PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000

inductive Arithmetic where
  | add | subtract | multiply | divide
  deriving DecidableEq

def Arithmetic.apply : Arithmetic → ℚ → ℚ → ℚ
  | .add,a,b => a+b
  | .subtract,a,b => a-b
  | .multiply,a,b => a*b
  | .divide,a,b => a/b

inductive Event where
  | copy (q : ℚ)
  | arithmetic (op : Arithmetic) (a b : ℚ)
  | compare (a b : ℚ)
  | control (word : ℕ)

abbrev Trace := List Event

def Event.price (model : RationalCostModel) : Event → ℕ
  | .copy q => 1+rationalWordWidth q
  | .arithmetic .divide a b => 1+2*model.rat (max (rationalWordWidth a) (rationalWordWidth b))
  | .arithmetic _ a b | .compare a b => 1+model.rat (max (rationalWordWidth a) (rationalWordWidth b))
  | .control n => 1+binaryWordWidth n

def price (model : RationalCostModel) (trace : Trace) : ℕ := (trace.map (Event.price model)).sum

def Event.Fits (W : ℕ) : Event → Prop
  | .copy q => rationalWordWidth q≤W
  | .arithmetic _ a b | .compare a b => rationalWordWidth a≤W ∧ rationalWordWidth b≤W
  | .control n => binaryWordWidth n≤W

def Fits (W : ℕ) (trace : Trace) : Prop := ∀ e∈trace,Event.Fits W e

theorem fits_mono {W V : ℕ} {trace : Trace} (h : Fits W trace) (hWV : W≤V) : Fits V trace := by
  intro e he
  have hfit := h e he
  cases e with
  | copy q => exact hfit.trans hWV
  | control n => exact hfit.trans hWV
  | arithmetic op a b => exact ⟨hfit.1.trans hWV,hfit.2.trans hWV⟩
  | compare a b => exact ⟨hfit.1.trans hWV,hfit.2.trans hWV⟩

theorem event_price (model : RationalCostModel) (W : ℕ) (hW : 1≤W) (event : Event) (h : event.Fits W) :
    event.price model≤3*model.rat W := by
  have hr : 1≤model.rat W := hW.trans (model.word_le W)
  cases event with
  | copy q =>
    have hq := h.trans (model.word_le W)
    change 1+rationalWordWidth q≤_
    omega
  | control n =>
    have hn := h.trans (model.word_le W)
    change 1+binaryWordWidth n≤_
    omega
  | arithmetic op a b =>
    have hp := model.monotone (max_le h.1 h.2)
    cases op <;> simp only [Event.price] <;> omega
  | compare a b =>
    have hp := model.monotone (max_le h.1 h.2)
    change 1+model.rat (max (rationalWordWidth a) (rationalWordWidth b))≤_
    omega

theorem price_bound (model : RationalCostModel) (W : ℕ) (hW : 1≤W) (trace : Trace) (h : Fits W trace) :
    price model trace≤3*trace.length*model.rat W := by
  induction trace with
  | nil => simp only [price,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons e trace ih =>
    have he := event_price model W hW e (h e List.mem_cons_self)
    have ht := ih (fun event hm => h event (List.mem_cons_of_mem e hm))
    simp only [price,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    nlinarith

theorem fits_append (W : ℕ) (a b : Trace) : Fits W (a++b) ↔ Fits W a ∧ Fits W b := by
  simp only [Fits,List.mem_append,or_imp,forall_and]

theorem price_append (model : RationalCostModel) (a b : Trace) : price model (a++b)=price model a+price model b := by
  simp only [price,List.map_append,List.sum_append]

def scalar (op : Arithmetic) (a b : ℚ) : ℚ×Trace :=
  let q := op.apply a b
  (q,[.copy a,.copy b,.arithmetic op a b,.copy q,.control 1])

def compare (a b : ℚ) : Bool×Trace :=
  (decide (a≤b),[.copy a,.copy b,.compare a b,.control 1])

def equalZero (a : ℚ) : Bool×Trace :=
  (decide (a=0),[.copy a,.compare a 0,.control 1])

def copyRow (row : List ℚ) : Trace := .control row.length::row.map Event.copy

theorem scalar_value (op : Arithmetic) (a b : ℚ) : (scalar op a b).1=op.apply a b := rfl
theorem scalar_length (op : Arithmetic) (a b : ℚ) : (scalar op a b).2.length=5 := rfl
theorem compare_length (a b : ℚ) : (compare a b).2.length=4 := rfl
theorem equalZero_length (a : ℚ) : (equalZero a).2.length=3 := rfl
theorem copyRow_length (row : List ℚ) : (copyRow row).length=row.length+1 := by
  simp only [copyRow,List.length_cons,List.length_map]

theorem scalar_fits (W : ℕ) (op : Arithmetic) (a b : ℚ)
    (ha : rationalWordWidth a≤W) (hb : rationalWordWidth b≤W)
    (hq : rationalWordWidth (op.apply a b)≤W) (hW : 1≤W) : Fits W (scalar op a b).2 := by
  intro e he
  simp only [scalar,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact ⟨ha,hb⟩
  · exact hq
  · exact hW

theorem compare_fits (W : ℕ) (a b : ℚ) (ha : rationalWordWidth a≤W) (hb : rationalWordWidth b≤W)
    (hW : 1≤W) : Fits W (compare a b).2 := by
  intro e he
  simp only [compare,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact ⟨ha,hb⟩
  · exact hW

theorem equalZero_fits (W : ℕ) (a : ℚ) (ha : rationalWordWidth a≤W)
    (hzero : rationalWordWidth (0:ℚ)≤W) (hW : 1≤W) : Fits W (equalZero a).2 := by
  intro e he
  simp only [equalZero,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl
  · exact ha
  · exact ⟨ha,hzero⟩
  · exact hW

theorem control_width (n : ℕ) : binaryWordWidth n≤n+1 := Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem copyRow_fits (W : ℕ) (row : List ℚ) (h : ∀ q∈row,rationalWordWidth q≤W)
    (hn : row.length+1≤W) : Fits W (copyRow row) := by
  intro e he
  rcases List.mem_cons.mp he with he | ht
  · subst e
    exact (control_width row.length).trans hn
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
    exact h q hq

theorem scalar_height (op : Arithmetic) (a b : ℚ) (H : ℕ) (ha : RationalHeight a H) (hb : RationalHeight b H) :
    RationalHeight (op.apply a b) (2*H+1) := by
  cases op with
  | add => simpa only [Arithmetic.apply,two_mul] using ha.add hb
  | subtract => simpa only [Arithmetic.apply,two_mul] using ha.sub hb
  | multiply => exact (ha.mul hb).mono (by omega)
  | divide => exact (ha.div hb).mono (by omega)

theorem scalar_fits_height (op : Arithmetic) (a b : ℚ) (H : ℕ) (ha : RationalHeight a H) (hb : RationalHeight b H) :
    Fits (4*H+3) (scalar op a b).2 := by
  have hq := rationalWordWidth_of_height (scalar_height op a b H ha hb)
  apply scalar_fits
  · exact (rationalWordWidth_of_height ha).trans (by omega)
  · exact (rationalWordWidth_of_height hb).trans (by omega)
  · omega
  · omega

end Blotto.PlayerSpecificRationalTrace
