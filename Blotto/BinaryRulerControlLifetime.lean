import Blotto.BinaryPositiveWordLifetime
import Blotto.BinaryRulerPrecision
import Blotto.BinaryPRGOutputLifetime

/-! Actual Boolean cursor cancellation, length/lexicographic comparison and
false mapping. Cancellation shares a suffix and comparisons stop at their
first decision; no represented integer or word-width counter is assembled. -/
namespace Blotto.BinaryRulerControlLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def differenceWithTrace : List Bool → List Bool → List Bool × Trace
  | bits, [] => (bits,wrap 8 1 [])
  | [], _::_ => ([],wrap 8 1 [])
  | _::bits, _::other =>
      let later := differenceWithTrace bits other
      (later.1,wrap 8 1 [later.2])

theorem differenceWithTrace_state (bits other : List Bool) :
    (differenceWithTrace bits other).1 = BinaryRulerPrecision.difference bits other := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => exact ih tail

theorem differenceWithTrace_usage (bits other : List Bool) : usage (differenceWithTrace bits other).2 ≤ 16*(bits.length+1) := by
  induction bits generalizing other with
  | nil => cases other <;> exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih => cases other with
    | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
    | cons head tail =>
        have ht := ih tail
        have hw := wrap_usage 8 1 [(differenceWithTrace rest tail).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 8 1 [(differenceWithTrace rest tail).2]) ≤ _
        simp only [List.length_cons]
        omega

def compareLengthWithTrace : List Bool → List Bool → Ordering × Trace
  | [], [] => (.eq,wrap 8 1 [])
  | [], _::_ => (.lt,wrap 8 1 [])
  | _::_, [] => (.gt,wrap 8 1 [])
  | _::bits, _::other =>
      let later := compareLengthWithTrace bits other
      (later.1,wrap 8 1 [later.2])

theorem compareLengthWithTrace_state (bits other : List Bool) :
    (compareLengthWithTrace bits other).1 = BinaryRulerPrecision.compareLength bits other := by
  induction bits generalizing other with
  | nil => cases other <;> rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => exact ih tail

theorem compareLengthWithTrace_usage (bits other : List Bool) :
    usage (compareLengthWithTrace bits other).2 ≤ 16*(bits.length+1) := by
  induction bits generalizing other with
  | nil => cases other <;> exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih => cases other with
    | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
    | cons head tail =>
        have ht := ih tail
        have hw := wrap_usage 8 1 [(compareLengthWithTrace rest tail).2]
        simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
        change usage (wrap 8 1 [(compareLengthWithTrace rest tail).2]) ≤ _
        simp only [List.length_cons]
        omega

def leScanWithTrace : List Bool → List Bool → Bool × Trace
  | [], _ => (true,wrap 8 1 [])
  | _::_, [] => (false,wrap 8 1 [])
  | a::bits, b::other =>
      if a = b then
        let later := leScanWithTrace bits other
        (later.1,wrap 8 1 [later.2])
      else (!a,wrap 8 1 [])

theorem leScanWithTrace_state (bits other : List Bool) : (leScanWithTrace bits other).1 = PositiveBinaryWord.leScan bits other := by
  induction bits generalizing other with
  | nil => rfl
  | cons bit rest ih => cases other with
    | nil => rfl
    | cons head tail => simp only [leScanWithTrace,PositiveBinaryWord.leScan]; split <;> simp only [ih]

theorem leScanWithTrace_usage (bits other : List Bool) : usage (leScanWithTrace bits other).2 ≤ 16*(bits.length+1) := by
  induction bits generalizing other with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih => cases other with
    | nil => exact (wrap_usage 8 1 []).trans (by simp <;> omega)
    | cons head tail =>
        unfold leScanWithTrace
        split
        · have ht := ih tail
          have hw := wrap_usage 8 1 [(leScanWithTrace rest tail).2]
          simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
          change usage (wrap 8 1 [(leScanWithTrace rest tail).2]) ≤ _
          simp only [List.length_cons]
          omega
        · exact (wrap_usage 8 1 []).trans (by simp <;> omega)

def falseMapWithTrace : List Bool → List Bool × Trace
  | [] => ([],wrap 8 1 [])
  | _::rest =>
      let later := falseMapWithTrace rest
      (false::later.1,wrapList 1 8 1 [later.2])

theorem falseMapWithTrace_state (bits : List Bool) : (falseMapWithTrace bits).1 = bits.map (fun _ => false) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp only [falseMapWithTrace,List.map_cons,ih]

theorem falseMapWithTrace_usage (bits : List Bool) : usage (falseMapWithTrace bits).2 ≤ 16*(bits.length+1) := by
  induction bits with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons bit rest ih =>
      have hw := wrapList_usage 1 8 1 [(falseMapWithTrace rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrapList 1 8 1 [(falseMapWithTrace rest).2]) ≤ _
      simp only [List.length_cons]
      omega

theorem append_usage (left right : List Bool) :
    usage (BinaryPRGOutputLifetime.appendWithTrace left right).2 ≤ 2*left.length+1 := by
  have hc := BinaryPRGOutputLifetime.appendWithTrace_cells left right
  have ha := BinaryPRGOutputLifetime.appendWithTrace_arrays left right
  have hf := BinaryPRGOutputLifetime.appendWithTrace_frames left right
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

end Blotto.BinaryRulerControlLifetime
