import Blotto.BinaryNativeRowEncoder

/-! A backwards tail loop copies a stored value reference and a tail link into each list cell.
The declared reference-machine profile charges the index/control word and
the referenced address separately; rational payloads are borrowed unchanged.
This is not a generated-C allocator or reference-count cost theorem. -/

namespace Blotto.StoredArrayReferenceList
set_option autoImplicit false

def into {α : Type*} (data : Array α) : (remaining : ℕ) → remaining ≤ data.size → List α → List α
  | 0, _, suffix => suffix
  | remaining+1, h, suffix =>
      into data remaining (by omega) (data[remaining]'(by omega)::suffix)

theorem into_data {α : Type*} (data : Array α) (remaining : ℕ) (h : remaining ≤ data.size) (suffix : List α) :
    into data remaining h suffix = data.toList.take remaining ++ suffix := by
  induction remaining generalizing suffix with
  | zero => rfl
  | succ remaining ih =>
    rw [into, ih, List.take_succ_eq_append_getElem (by simpa using h : remaining < data.toList.length)]
    simp only [Array.getElem_toList, List.append_assoc, List.singleton_append]

def list {α : Type*} (data : Array α) : List α := into data data.size (Nat.le_refl _) []

theorem list_data {α : Type*} (data : Array α) : list data = data.toList := by
  rw [list, into_data, List.append_nil]
  simpa only [Array.length_toList] using (List.take_length (l := data.toList))

def work (primitive : ℕ → ℕ) (addressWidth : ℕ) : ℕ → ℕ
  | 0 => primitive 1+1
  | remaining+1 => work primitive addressWidth remaining+
      4*primitive (binaryWordWidth (remaining+1)+1)+2*addressWidth+4

theorem work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (addressWidth remaining : ℕ) :
    work primitive addressWidth remaining ≤
      remaining*(4*c*(binaryWordWidth remaining+1)+2*addressWidth+4)+c+1 := by
  induction remaining with
  | zero =>
    have h := hPrimitive 1
    simp only [work, Nat.zero_mul, Nat.zero_add]
    omega
  | succ remaining ih =>
    have hp := hPrimitive (binaryWordWidth (remaining+1)+1)
    have hm := Nat.mul_le_mul_left (remaining*(4*c))
      (Nat.add_le_add_right (binaryWordWidth_mono (Nat.le_succ remaining)) 1)
    rw [work]
    nlinarith only [ih,hp,hm]

/- Each reached iteration has the same one-cell allocation and the final
tail loop retains the input array plus its growing output, without a recursive
activation stack in the declared machine. -/
def allocatedCells (remaining : ℕ) : ℕ := remaining

def retainedReferences (inputSize suffixSize used : ℕ) : ℕ := inputSize+2*(suffixSize+used)

theorem into_length {α : Type*} (data : Array α) (remaining : ℕ) (h : remaining ≤ data.size) (suffix : List α) :
    (into data remaining h suffix).length = remaining+suffix.length := by
  rw [into_data, List.length_append, List.length_take]
  simp only [Array.length_toList]
  omega

theorem prefix_references (inputSize suffixSize used remaining : ℕ) (h : used ≤ remaining)
    (hSize : remaining ≤ inputSize) :
    retainedReferences inputSize suffixSize used ≤ 3*inputSize+2*suffixSize := by
  unfold retainedReferences
  omega

theorem prefix_reference_bits (inputSize suffixSize used remaining addressWidth : ℕ)
    (h : used ≤ remaining) (hSize : remaining ≤ inputSize) :
    addressWidth*retainedReferences inputSize suffixSize used ≤
      addressWidth*(3*inputSize+2*suffixSize) :=
  Nat.mul_le_mul_left addressWidth (prefix_references inputSize suffixSize used remaining h hSize)

theorem concrete_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (n : ℕ) :
    work primitive (binaryWordWidth (n+1)) n ≤
      (5*c+6)*(n+1)*(binaryWordWidth (n+1)+1) := by
  have h := work_bound primitive c hPrimitive (binaryWordWidth (n+1)) n
  have hm := Nat.mul_le_mul_left (n*(4*c))
    (Nat.add_le_add_right (binaryWordWidth_mono (Nat.le_succ n)) 1)
  nlinarith only [h,hm]

def poolAddressWidth (n W : ℕ) : ℕ := binaryWordWidth (n*(W+1)+1)

theorem poolAddressWidth_log_bound (n W : ℕ) :
    poolAddressWidth n W ≤ binaryWordWidth (n+1)+binaryWordWidth (W+1) := by
  have hn : n*(W+1)+1 ≤ (n+1)*(W+1) := by nlinarith
  exact (binaryWordWidth_mono hn).trans (binaryWordWidth_mul (n+1) (W+1))

theorem poolAddressWidth_linear_bound (n W : ℕ) (h : n ≤ W) : poolAddressWidth n W ≤ 2*W+4 := by
  have hp := poolAddressWidth_log_bound n W
  have hm := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  have hl := Nat.log2_le_self (W+1)
  unfold binaryWordWidth at hp hm
  omega

theorem pool_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (n W : ℕ) :
    work primitive (poolAddressWidth n W) n ≤
      (5*c+6)*(n+1)*(poolAddressWidth n W+1) := by
  have h := work_bound primitive c hPrimitive (poolAddressWidth n W) n
  have hn : n ≤ n*(W+1)+1 := by nlinarith
  have hw := binaryWordWidth_mono hn
  change binaryWordWidth n ≤ poolAddressWidth n W at hw
  have hm := Nat.mul_le_mul_left (n*(4*c)) (Nat.add_le_add_right hw 1)
  nlinarith only [h,hm]

structure Cursor {α : Type*} (data : Array α) where
  remaining : ℕ
  bounded : remaining ≤ data.size
  tail : List α

def next {α : Type*} (data : Array α) (cursor : Cursor data) : Cursor data :=
  match cursor with
  | ⟨0,h,tail⟩ => ⟨0,h,tail⟩
  | ⟨remaining+1,h,tail⟩ => ⟨remaining,by omega,data[remaining]'(by omega)::tail⟩

theorem next_mass {α : Type*} (data : Array α) (cursor : Cursor data) :
    (next data cursor).remaining+(next data cursor).tail.length = cursor.remaining+cursor.tail.length := by
  rcases cursor with ⟨remaining,h,tail⟩
  cases remaining <;> simp only [next, List.length_cons] <;> omega

theorem next_continuation {α : Type*} (data : Array α) (cursor : Cursor data) :
    into data (next data cursor).remaining (next data cursor).bounded (next data cursor).tail =
      into data cursor.remaining cursor.bounded cursor.tail := by
  rcases cursor with ⟨remaining,h,tail⟩
  cases remaining <;> rfl

def advance {α : Type*} (data : Array α) : ℕ → Cursor data → Cursor data
  | 0, cursor => cursor
  | used+1, cursor => next data (advance data used cursor)

theorem advance_mass {α : Type*} (data : Array α) (used : ℕ) (cursor : Cursor data) :
    (advance data used cursor).remaining+(advance data used cursor).tail.length =
      cursor.remaining+cursor.tail.length := by
  induction used with
  | zero => rfl
  | succ used ih =>
    change (next data (advance data used cursor)).remaining+(next data (advance data used cursor)).tail.length = _
    rw [next_mass, ih]

theorem advance_continuation {α : Type*} (data : Array α) (used : ℕ) (cursor : Cursor data) :
    into data (advance data used cursor).remaining (advance data used cursor).bounded (advance data used cursor).tail =
      into data cursor.remaining cursor.bounded cursor.tail := by
  induction used with
  | zero => rfl
  | succ used ih =>
    change into data (next data (advance data used cursor)).remaining
      (next data (advance data used cursor)).bounded (next data (advance data used cursor)).tail = _
    rw [next_continuation, ih]

theorem every_prefix_references {α : Type*} (data : Array α) (used : ℕ) (cursor : Cursor data) :
    data.size+2*(advance data used cursor).tail.length ≤ 3*data.size+2*cursor.tail.length := by
  have h := advance_mass data used cursor
  have hs := cursor.bounded
  omega

theorem every_prefix_reference_bits {α : Type*} (data : Array α) (used addressWidth : ℕ) (cursor : Cursor data) :
    addressWidth*(data.size+2*(advance data used cursor).tail.length) ≤
      addressWidth*(3*data.size+2*cursor.tail.length) :=
  Nat.mul_le_mul_left addressWidth (every_prefix_references data used cursor)

theorem every_prefix_counter_width {α : Type*} (data : Array α) (used : ℕ) (cursor : Cursor data) :
    binaryWordWidth (advance data used cursor).remaining ≤ binaryWordWidth data.size :=
  binaryWordWidth_mono (advance data used cursor).bounded

theorem every_prefix_payload_and_references {α : Type*} (data : Array α)
    (used addressWidth payloadBits : ℕ) (cursor : Cursor data) :
    payloadBits+addressWidth*(data.size+2*(advance data used cursor).tail.length) ≤
      payloadBits+addressWidth*(3*data.size+2*cursor.tail.length) :=
  Nat.add_le_add_left (every_prefix_reference_bits data used addressWidth cursor) payloadBits

end Blotto.StoredArrayReferenceList
