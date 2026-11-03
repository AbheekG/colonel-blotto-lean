import Blotto.BinaryRulerControlLifetime

/-! The scheduled sample count is produced by Boolean carries over actual
row and precision cells. No numerical dimension/precision or natural arithmetic
producer is called. The fixed 3000 overhead is resident constant Boolean data.
Copies are explicit and priced; counter value/width are proof interpretations. -/
namespace Blotto.BooleanSampleCountLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def initial : List Bool := [false,false,false,true,true,true,false,true,true,true,false,true]

theorem initial_value : BinaryCarryCounter.value initial = 3000 := by decide

theorem initial_canonical : BinaryCarryCounter.Canonical initial := by simp [initial,BinaryCarryCounter.Canonical]

def rowRulerWithTrace {α : Type*} : List α → List Bool × Trace
  | [] => ([],wrap 8 1 [])
  | _::rest =>
      let later := rowRulerWithTrace rest
      (false::later.1,wrapList 1 8 1 [later.2])

theorem rowRuler_length {α : Type*} (rows : List α) : (rowRulerWithTrace rows).1.length = rows.length := by
  induction rows with
  | nil => rfl
  | cons item rest ih => simp only [rowRulerWithTrace,List.length_cons,ih]

theorem rowRuler_usage {α : Type*} (rows : List α) : usage (rowRulerWithTrace rows).2 ≤ 16*(rows.length+1) := by
  induction rows with
  | nil => exact (wrap_usage 8 1 []).trans (by simp)
  | cons item rest ih =>
      have hw := wrapList_usage 1 8 1 [(rowRulerWithTrace rest).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrapList 1 8 1 [(rowRulerWithTrace rest).2]) ≤ _
      simp only [List.length_cons]
      omega

def scheduleWithTrace {α : Type*} (rows : List α) (ruler : List Bool) : List Bool × Trace :=
  let fields := rowRulerWithTrace rows
  let fields2 := BinaryPRGOutputLifetime.appendWithTrace fields.1 fields.1
  let fields3 := BinaryPRGOutputLifetime.appendWithTrace fields.1 fields2.1
  let precision2 := BinaryPRGOutputLifetime.appendWithTrace ruler ruler
  let precision4 := BinaryPRGOutputLifetime.appendWithTrace precision2.1 precision2.1
  let precision5 := BinaryPRGOutputLifetime.appendWithTrace ruler precision4.1
  let joined := BinaryPRGOutputLifetime.appendWithTrace fields3.1 precision5.1
  (joined.1,wrap 96 2 [fields.2,fields2.2,fields3.2,precision2.2,precision4.2,precision5.2,joined.2])

theorem schedule_length {α : Type*} (rows : List α) (ruler : List Bool) :
    (scheduleWithTrace rows ruler).1.length = 3*rows.length+5*ruler.length := by
  simp only [scheduleWithTrace,BinaryPRGOutputLifetime.appendWithTrace_state,List.length_append,rowRuler_length]
  omega

theorem schedule_usage {α : Type*} (rows : List α) (ruler : List Bool) :
    usage (scheduleWithTrace rows ruler).2 ≤ 256*(rows.length+ruler.length+1) := by
  let fields := rowRulerWithTrace rows
  let fields2 := BinaryPRGOutputLifetime.appendWithTrace fields.1 fields.1
  let fields3 := BinaryPRGOutputLifetime.appendWithTrace fields.1 fields2.1
  let precision2 := BinaryPRGOutputLifetime.appendWithTrace ruler ruler
  let precision4 := BinaryPRGOutputLifetime.appendWithTrace precision2.1 precision2.1
  let precision5 := BinaryPRGOutputLifetime.appendWithTrace ruler precision4.1
  have h0 := rowRuler_usage rows
  have h1 := BinaryRulerControlLifetime.append_usage fields.1 fields.1
  have h2 := BinaryRulerControlLifetime.append_usage fields.1 fields2.1
  have h3 := BinaryRulerControlLifetime.append_usage ruler ruler
  have h4 := BinaryRulerControlLifetime.append_usage precision2.1 precision2.1
  have h5 := BinaryRulerControlLifetime.append_usage ruler precision4.1
  have h6 := BinaryRulerControlLifetime.append_usage fields3.1 precision5.1
  have hw := wrap_usage 96 2 [fields.2,fields2.2,fields3.2,precision2.2,precision4.2,precision5.2,
    (BinaryPRGOutputLifetime.appendWithTrace fields3.1 precision5.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (scheduleWithTrace rows ruler).2 ≤ _ at hw
  change usage fields.2 ≤ _ at h0
  change usage fields2.2 ≤ _ at h1
  change usage fields3.2 ≤ _ at h2
  change usage precision2.2 ≤ _ at h3
  change usage precision4.2 ≤ _ at h4
  change usage precision5.2 ≤ _ at h5
  have hf : fields.1.length = rows.length := rowRuler_length rows
  have hp : precision2.1.length = 2*ruler.length := by simp only [precision2,BinaryPRGOutputLifetime.appendWithTrace_state,List.length_append]; omega
  have hff : fields3.1.length = 3*rows.length := by
    simp only [fields3,fields2,BinaryPRGOutputLifetime.appendWithTrace_state,List.length_append,hf]
    omega
  omega

theorem ones_le_length (counter : List Bool) : BinaryCarryCounter.ones counter ≤ counter.length := by
  induction counter with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [BinaryCarryCounter.ones,List.length_cons] <;> omega

theorem count_usage {α : Type*} (items : List α) (counter : List Bool) :
    usage (BinaryWordStoreLifetime.countWithTrace items counter).2 ≤ 32*(items.length+counter.length+1) := by
  have h := BinaryWordStoreLifetime.countWithTrace_bounds items counter
  have hc := BinaryCarryCounter.countCarryCells_bound items counter
  have ho := ones_le_length counter
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

def prepareWithTrace {α : Type*} (rows : List α) (ruler : List Bool) : List Bool × Trace :=
  let schedule := scheduleWithTrace rows ruler
  let counted := BinaryWordStoreLifetime.countWithTrace schedule.1 initial
  (counted.1,wrapList 12 32 2 [schedule.2,counted.2])

theorem prepare_value {α : Type*} (rows : List α) (ruler : List Bool) :
    BinaryCarryCounter.value (prepareWithTrace rows ruler).1 = 3*rows.length+5*ruler.length+3000 := by
  simp only [prepareWithTrace,BinaryWordStoreLifetime.countWithTrace_erases,BinaryCarryCounter.count_value,
    initial_value,schedule_length]
  omega

theorem prepare_canonical {α : Type*} (rows : List α) (ruler : List Bool) :
    BinaryCarryCounter.Canonical (prepareWithTrace rows ruler).1 := by
  simp only [prepareWithTrace,BinaryWordStoreLifetime.countWithTrace_erases]
  exact BinaryCarryCounter.count_canonical _ initial initial_canonical

theorem prepare_width {α : Type*} (rows : List α) (ruler : List Bool) :
    (prepareWithTrace rows ruler).1.length ≤ binaryWordWidth (3*rows.length+5*ruler.length+3000) := by
  have h := BinaryCarryCounter.canonical_length_bound _ (prepare_canonical rows ruler)
  rw [prepare_value] at h
  exact h

theorem prepare_usage {α : Type*} (rows : List α) (ruler : List Bool) :
    usage (prepareWithTrace rows ruler).2 ≤ 1000*(rows.length+ruler.length+16) := by
  have hs := schedule_usage rows ruler
  have hc := count_usage (scheduleWithTrace rows ruler).1 initial
  have hw := wrapList_usage 12 32 2 [(scheduleWithTrace rows ruler).2,
    (BinaryWordStoreLifetime.countWithTrace (scheduleWithTrace rows ruler).1 initial).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  rw [schedule_length] at hc
  change usage (prepareWithTrace rows ruler).2 ≤ _ at hw
  rw [show initial.length = 12 from rfl] at hc
  omega

end Blotto.BooleanSampleCountLifetime
