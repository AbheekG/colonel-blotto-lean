import Blotto.BinaryRulerPrecisionWork
import Blotto.BinaryWordCoinPrimitivesMeasured

/-! One Boolean cancellation/comparison/false-map execution returns the
actual data, old lifetime trace and source work together. Numeric values and
width countdowns are absent from the producer. Observer/native reference and
allocator costs remain separate from these Boolean/list source charges. -/
namespace Blotto.BinaryRulerControlMeasured
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def difference : List Bool → List Bool → (List Bool × Trace) × ℕ
  | bits,[] => ((bits,wrap 8 1 []),2)
  | [],_::_ => (([],wrap 8 1 []),2)
  | _::bits,_::other =>
      let later := difference bits other
      ((later.1.1,wrap 8 1 [later.1.2]),later.2+4)

theorem difference_erases (bits other : List Bool) :
    (difference bits other).1 = BinaryRulerControlLifetime.differenceWithTrace bits other := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other => simp only [difference,BinaryRulerControlLifetime.differenceWithTrace,ih]

theorem difference_charge (bits other : List Bool) :
    (difference bits other).2 = (BinaryRulerPrecisionWork.differenceWithWork bits other).2 := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other => simp only [difference,BinaryRulerPrecisionWork.differenceWithWork,ih]

theorem difference_work (bits other : List Bool) : (difference bits other).2 ≤ 4*(bits.length+1) := by
  rw [difference_charge]
  exact BinaryRulerPrecisionWork.difference_work bits other

def compareLength : List Bool → List Bool → (Ordering × Trace) × ℕ
  | [],[] => ((.eq,wrap 8 1 []),2)
  | [],_::_ => ((.lt,wrap 8 1 []),2)
  | _::_,[] => ((.gt,wrap 8 1 []),2)
  | _::bits,_::other =>
      let later := compareLength bits other
      ((later.1.1,wrap 8 1 [later.1.2]),later.2+4)

theorem compareLength_erases (bits other : List Bool) :
    (compareLength bits other).1 = BinaryRulerControlLifetime.compareLengthWithTrace bits other := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other => simp only [compareLength,BinaryRulerControlLifetime.compareLengthWithTrace,ih]

theorem compareLength_charge (bits other : List Bool) :
    (compareLength bits other).2 = (BinaryRulerPrecisionWork.compareLengthWithWork bits other).2 := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other => simp only [compareLength,BinaryRulerPrecisionWork.compareLengthWithWork,ih]

theorem compareLength_work (bits other : List Bool) : (compareLength bits other).2 ≤ 4*(bits.length+1) := by
  rw [compareLength_charge]
  exact BinaryRulerPrecisionWork.compareLength_work bits other

def leScan : List Bool → List Bool → (Bool × Trace) × ℕ
  | [],_ => ((true,wrap 8 1 []),2)
  | _::_,[] => ((false,wrap 8 1 []),2)
  | a::bits,b::other =>
      if a = b then
        let later := leScan bits other
        ((later.1.1,wrap 8 1 [later.1.2]),later.2+5)
      else ((!a,wrap 8 1 []),5)

theorem leScan_erases (bits other : List Bool) :
    (leScan bits other).1 = BinaryRulerControlLifetime.leScanWithTrace bits other := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other =>
        simp only [leScan,BinaryRulerControlLifetime.leScanWithTrace]
        split <;> simp only [ih]

theorem leScan_charge (bits other : List Bool) :
    (leScan bits other).2 = (BinaryRulerPrecisionWork.leScanWithWork bits other).2 := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit bits ih => cases other with
    | nil => rfl
    | cons head other =>
        simp only [leScan,BinaryRulerPrecisionWork.leScanWithWork]
        split <;> simp only [ih]

theorem leScan_work (bits other : List Bool) : (leScan bits other).2 ≤ 5*bits.length+2 := by
  rw [leScan_charge]
  exact BinaryRulerPrecisionWork.leScan_work bits other

def falseMap : List Bool → (List Bool × Trace) × ℕ
  | [] => (([],wrap 8 1 []),2)
  | _::rest =>
      let later := falseMap rest
      ((false::later.1.1,wrapList 1 8 1 [later.1.2]),later.2+4)

theorem falseMap_erases (bits : List Bool) :
    (falseMap bits).1 = BinaryRulerControlLifetime.falseMapWithTrace bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMap,BinaryRulerControlLifetime.falseMapWithTrace,ih]

theorem falseMap_work (bits : List Bool) : (falseMap bits).2 = 4*bits.length+2 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMap,ih,List.length_cons]; omega

theorem falseMap_length (bits : List Bool) : (falseMap bits).1.1.length = bits.length := by
  rw [falseMap_erases,BinaryRulerControlLifetime.falseMapWithTrace_state,List.length_map]

end Blotto.BinaryRulerControlMeasured
