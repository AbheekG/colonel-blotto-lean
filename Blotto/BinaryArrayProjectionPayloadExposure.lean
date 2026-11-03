import Blotto.BinaryArrayProjectionLifetime
import Blotto.BinaryPRGFrameCostJoin
import Blotto.BinaryPRGRawRequestLifetime

/-! Exact payload-width sum of words visited by the descending input-value
array reader. This measures the represented word contents once per native get;
native borrowed-reference transport, pointer width and allocator behavior are
separate. -/
namespace Blotto.BinaryArrayProjectionPayloadExposure
open BinaryRationalNormalization
open scoped BigOperators

def loopWithPayload (payload : SignedWord → ℕ) (data : Array SignedWord) (acc : List SignedWord) :
    (remaining : ℕ) → remaining ≤ data.size → List SignedWord × ℕ
  | 0,_ => (acc,0)
  | remaining+1,h =>
      let word := data[remaining]'(by omega)
      let later := loopWithPayload payload data (word::acc) remaining (by omega)
      (later.1,later.2+payload word)

theorem loop_state (payload : SignedWord → ℕ) (data : Array SignedWord) (acc : List SignedWord)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithPayload payload data acc remaining h).1 =
      (BinaryArrayProjectionLifetime.loopWithTrace data acc remaining h).1 := by
  induction remaining generalizing acc with
  | zero => rfl
  | succ remaining ih => exact ih (data[remaining]'(by omega)::acc) (by omega)

theorem loop_sum (payload : SignedWord → ℕ) (data : Array SignedWord) (acc : List SignedWord)
    (remaining : ℕ) (h : remaining ≤ data.size) :
    (loopWithPayload payload data acc remaining h).2 =
      ((data.toList.take remaining).map payload).sum := by
  induction remaining generalizing acc with
  | zero => simp [loopWithPayload]
  | succ remaining ih =>
      have hIndex : remaining < data.toList.length := by
        simp only [Array.length_toList]
        omega
      have hTake := List.take_concat_get' data.toList remaining hIndex
      simp only [loopWithPayload,ih]
      rw [← hTake,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]
      simp only [Array.getElem_toList]

def readWithPayload (payload : SignedWord → ℕ) (data : Array SignedWord) : List SignedWord × ℕ :=
  loopWithPayload payload data [] data.size (Nat.le_refl _)

theorem read_state (payload : SignedWord → ℕ) (data : Array SignedWord) :
    (readWithPayload payload data).1 = (BinaryArrayProjectionLifetime.readWithTrace data).1 :=
  loop_state payload data [] _ _

theorem read_sum (payload : SignedWord → ℕ) (data : Array SignedWord) :
    (readWithPayload payload data).2 = (data.toList.map payload).sum := by
  rw [readWithPayload,loop_sum]
  rw [show data.size = data.toList.length by simp,List.take_length]

theorem array_sum (payload : SignedWord → ℕ) (data : Array SignedWord) :
    (data.toList.map payload).sum = ∑ j : Fin data.size, payload data[j.val] := by
  rw [← List.sum_ofFn]
  change (data.toList.map payload).sum =
    (List.ofFn (payload ∘ fun j : Fin data.size => data[j.val])).sum
  rw [← List.map_ofFn]
  change (data.toList.map payload).sum =
    ((List.ofFn (fun j : Fin data.toList.length => data.toList[j.val])).map payload).sum
  rw [List.ofFn_getElem]

theorem table_sum (payload : SignedWord → ℕ) {n : ℕ} (table : FixedArrayTable n SignedWord) :
    (table.data.toList.map payload).sum = ∑ j : Fin n, payload (table.read j) := by
  rcases table with ⟨data,hSize⟩
  cases hSize
  simpa only [FixedArrayTable.read] using array_sum payload data

theorem raw_values_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (readWithPayload width parsed.1.2.request.prepared.original.values.data).2 ≤
      frame.length+2 := by
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hStored := BinaryPRGFrameCostJoin.read_stored_width frame parsed hOld
  have hSum := read_sum width parsed.1.2.request.prepared.original.values.data
  rw [table_sum width parsed.1.2.request.prepared.original.values] at hSum
  unfold BinaryPRGPreparationWork.storedInputWidth at hStored
  omega

def fieldBits (word : SignedWord) : ℕ :=
  1 + word.numerator.length + word.denominator.length

theorem fieldBits_le (word : SignedWord) : fieldBits word ≤ 1+2*width word := by
  have hn := Nat.le_max_left word.numerator.length word.denominator.length
  have hd := Nat.le_max_right word.numerator.length word.denominator.length
  unfold fieldBits width
  omega

theorem table_fieldBits_le {n : ℕ} (table : FixedArrayTable n SignedWord) :
    (∑ j : Fin n, fieldBits (table.read j)) ≤
      n + 2*(∑ j : Fin n, width (table.read j)) := by
  calc
    _ ≤ ∑ j : Fin n, (1+2*width (table.read j)) :=
      Finset.sum_le_sum (fun j _ => fieldBits_le (table.read j))
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]

theorem raw_fieldBits_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (readWithPayload fieldBits parsed.1.2.request.prepared.original.values.data).2 ≤
      3*frame.length+4 := by
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hStored := BinaryPRGFrameCostJoin.read_stored_width frame parsed hOld
  have hSum := read_sum fieldBits parsed.1.2.request.prepared.original.values.data
  rw [table_sum fieldBits parsed.1.2.request.prepared.original.values] at hSum
  have hFields := table_fieldBits_le parsed.1.2.request.prepared.original.values
  unfold BinaryPRGPreparationWork.storedInputWidth at hStored
  omega

end Blotto.BinaryArrayProjectionPayloadExposure
