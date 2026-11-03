import Blotto.GeneralPaperBooleanBorrow

/-! A prepared unary ruler controls the fresh word scan. Source operations
are bit calls, Boolean/list-cell reads/writes and sequential control; no
native numeric index or decoded rank controls the scan. A zero high bit
pads the result for comparison with the possibly power-of-two denominator. -/
namespace Blotto.GeneralPaperBooleanFreshWord
set_option autoImplicit false
set_option maxHeartbeats 700000

structure Result (S : Type*) where
  bits : List Bool
  state : S
  reads : ℕ
  work : ℕ

def collect {S : Type*} (next : S → Bool × S) : List Unit → List Bool → S → Result S
  | [], acc, state =>
    let returned := BinaryCompareBitsMeasured.reverse (false :: acc) []
    ⟨returned.1, state, 0, returned.2 + 4⟩
  | _ :: rest, acc, state =>
    let sampled := next state
    let later := collect next rest (sampled.1 :: acc) sampled.2
    ⟨later.bits, later.state, later.reads + 1, later.work + 6⟩

theorem collect_length {S : Type*} (next : S → Bool × S) (ruler : List Unit) (acc : List Bool) (state : S) :
    (collect next ruler acc state).bits.length = ruler.length + acc.length + 1 := by
  induction ruler generalizing acc state with
  | nil => simp [collect, BinaryCompareBitsMeasured.reverse_data, Nat.add_comm]
  | cons cell rest ih =>
    have h := ih ((next state).1 :: acc) (next state).2
    simp only [collect, List.length_cons] at h ⊢
    omega

theorem collect_reads {S : Type*} (next : S → Bool × S) (ruler : List Unit) (acc : List Bool) (state : S) :
    (collect next ruler acc state).reads = ruler.length := by
  induction ruler generalizing acc state with
  | nil => rfl
  | cons cell rest ih => exact congrArg (fun n => n + 1) (ih ((next state).1 :: acc) (next state).2)

theorem collect_work {S : Type*} (next : S → Bool × S) (ruler : List Unit) (acc : List Bool) (state : S) :
    (collect next ruler acc state).work = 10 * ruler.length + 4 * acc.length + 10 := by
  induction ruler generalizing acc state with
  | nil => simp [collect, BinaryCompareBitsMeasured.reverse_work]; omega
  | cons cell rest ih =>
    have h := ih ((next state).1 :: acc) (next state).2
    simp only [collect, List.length_cons] at h ⊢
    omega

def nextList : List Bool → Bool × List Bool
  | [] => (false, [])
  | b :: rest => (b, rest)

theorem collect_list (ruler : List Unit) (block suffix acc : List Bool) (h : block.length = ruler.length) :
    (collect nextList ruler acc (block ++ suffix)).bits = acc.reverse ++ block ++ [false] ∧
      (collect nextList ruler acc (block ++ suffix)).state = suffix := by
  induction ruler generalizing block acc with
  | nil =>
    have hp : block = [] := List.eq_nil_of_length_eq_zero h
    subst block
    simp [collect, BinaryCompareBitsMeasured.reverse_data]
  | cons cell rest ih => cases block with
    | nil => simp at h
    | cons bit tail =>
      have hh := ih tail (bit :: acc) (by simpa using h)
      simpa [collect, nextList, List.reverse_cons, List.append_assoc] using hh

def read {S : Type*} (next : S → Bool × S) (ruler : List Unit) (state : S) :
    (FixedBinaryWord (ruler.length + 1) × S) × ℕ × ℕ :=
  let result := collect next ruler [] state
  ((⟨result.bits, by simpa using collect_length next ruler [] state⟩, result.state), result.reads, result.work)

theorem read_counts {S : Type*} (next : S → Bool × S) (ruler : List Unit) (state : S) :
    (read next ruler state).2.1 = ruler.length ∧ (read next ruler state).2.2 = 10 * ruler.length + 10 := by
  exact ⟨collect_reads next ruler [] state, by simpa only [read, List.length_nil, Nat.mul_zero, Nat.add_zero] using collect_work next ruler [] state⟩

theorem read_list (ruler : List Unit) (block suffix : List Bool) (h : block.length = ruler.length) :
    (read nextList ruler (block ++ suffix)).1.1.bits = block ++ [false] ∧
      (read nextList ruler (block ++ suffix)).1.2 = suffix := by
  simpa only [read, List.reverse_nil, List.nil_append] using collect_list ruler block suffix [] h

theorem list_value (K : ℕ) (bits : Fin K → Bool) :
    BinaryBigEndian.littleValue (List.ofFn bits) = (bitIndex K bits).val := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [List.ofFn_succ]
    change 2 * BinaryBigEndian.littleValue (List.ofFn (Fin.tail bits)) + (if bits 0 then 1 else 0) =
      2 * (bitIndex K (Fin.tail bits)).val + (if bits 0 then 1 else 0)
    exact congrArg (fun n => 2 * n + if bits 0 then 1 else 0) (ih (Fin.tail bits))

theorem read_value (ruler : List Unit) (bits : Fin ruler.length → Bool) :
    (read nextList ruler (List.ofFn bits)).1.1.value = (balancedBitIndex ruler.length bits).val := by
  have h := read_list ruler (List.ofFn bits) [] (by simp)
  simp only [List.append_nil] at h
  change BinaryBigEndian.littleValue _ = _
  rw [h.1, BinaryWordHighBit.littleValue_append]
  simp only [BinaryBigEndian.littleValue, Nat.mul_zero, Nat.add_zero, Bool.false_eq_true, ite_false]
  rw [list_value, balancedBitIndex_eq]

end Blotto.GeneralPaperBooleanFreshWord
