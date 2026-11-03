import Blotto.StoredArrayReferenceList

/-! Table materialization copies references to an existing value pool.
The declared push profile permits copying its entire old prefix, with explicit
copy-counter/address work. It never copies a rational payload. Native array
ownership, allocator and reference-count calibration are separate. -/

namespace Blotto.ReferenceArrayBuilder
set_option autoImplicit false

def into {α : Type*} : List α → Array α → Array α
  | [],data => data
  | value::rest,data => into rest (data.push value)

theorem into_data {α : Type*} (values : List α) (data : Array α) :
    (into values data).toList = data.toList++values := by
  induction values generalizing data with
  | nil => simp only [into,List.append_nil]
  | cons value rest ih =>
    rw [into,ih]
    simp only [Array.toList_push,List.append_assoc,List.singleton_append]

def array {α : Type*} (values : List α) : Array α := into values #[]

theorem array_data {α : Type*} (values : List α) : array values = values.toArray := by
  apply Array.toList_inj.mp
  simp only [array,into_data,List.nil_append]

theorem into_size {α : Type*} (values : List α) (data : Array α) :
    (into values data).size = data.size+values.length := by
  have h := congrArg List.length (into_data values data)
  simpa only [Array.length_toList,List.length_append] using h

def pushWork (primitive : ℕ → ℕ) (addressWidth oldSize : ℕ) : ℕ :=
  (oldSize+1)*(4*addressWidth+4*primitive (binaryWordWidth (oldSize+1)+1)+12)

theorem push_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (addressWidth oldSize capacity : ℕ) (hSize : oldSize ≤ capacity) :
    pushWork primitive addressWidth oldSize ≤
      (capacity+1)*(4*addressWidth+4*c*(binaryWordWidth (capacity+1)+1)+12) := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right hSize 1)
  have hp := (hPrimitive (binaryWordWidth (oldSize+1)+1)).trans
    (Nat.mul_le_mul_left c (Nat.add_le_add_right hw 1))
  unfold pushWork
  exact Nat.mul_le_mul (Nat.add_le_add_right hSize 1) (by nlinarith only [hp])

def work {α : Type*} (primitive : ℕ → ℕ) (addressWidth : ℕ) : List α → ℕ → ℕ
  | [],_ => 1
  | _::rest,oldSize => pushWork primitive addressWidth oldSize+work primitive addressWidth rest (oldSize+1)

theorem work_bound {α : Type*} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (addressWidth capacity : ℕ) (values : List α) (start : ℕ) (hSize : start+values.length ≤ capacity) :
    work primitive addressWidth values start ≤
      values.length*(capacity+1)*(4*addressWidth+4*c*(binaryWordWidth (capacity+1)+1)+12)+1 := by
  induction values generalizing start with
  | nil => simp only [work,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons value rest ih =>
    have hr := ih (start+1) (by simp only [List.length_cons] at hSize; omega)
    have hp := push_work_bound primitive c hPrimitive addressWidth start capacity (by omega)
    simp only [work,List.length_cons]
    nlinarith only [hr,hp]

def next {α : Type*} : List α × Array α → List α × Array α
  | ([],data) => ([],data)
  | (value::rest,data) => (rest,data.push value)

theorem next_mass {α : Type*} (state : List α × Array α) :
    (next state).1.length+(next state).2.size = state.1.length+state.2.size := by
  rcases state with ⟨values,data⟩
  cases values <;> simp only [next,List.length_cons,Array.size_push] <;> omega

theorem next_continuation {α : Type*} (state : List α × Array α) :
    into (next state).1 (next state).2 = into state.1 state.2 := by
  rcases state with ⟨values,data⟩
  cases values <;> rfl

def advance {α : Type*} : ℕ → List α × Array α → List α × Array α
  | 0,state => state
  | used+1,state => next (advance used state)

theorem advance_mass {α : Type*} (used : ℕ) (state : List α × Array α) :
    (advance used state).1.length+(advance used state).2.size = state.1.length+state.2.size := by
  induction used with
  | zero => rfl
  | succ used ih =>
    change (next (advance used state)).1.length+(next (advance used state)).2.size = _
    rw [next_mass,ih]

theorem advance_continuation {α : Type*} (used : ℕ) (state : List α × Array α) :
    into (advance used state).1 (advance used state).2 = into state.1 state.2 := by
  induction used with
  | zero => rfl
  | succ used ih =>
    change into (next (advance used state)).1 (next (advance used state)).2 = _
    rw [next_continuation,ih]

theorem every_prefix_table_size {α : Type*} (used : ℕ) (values : List α) :
    (advance used (values,#[])).2.size ≤ values.length := by
  have h := advance_mass used (values,#[])
  simp only [Array.size_empty,Nat.add_zero] at h
  omega

theorem every_prefix_copy_references {α : Type*} (used addressWidth payloadBits : ℕ) (values : List α) :
    payloadBits+addressWidth*(2*((advance used (values,#[])).2.size+1)) ≤
      payloadBits+addressWidth*(2*(values.length+1)) := by
  have h := every_prefix_table_size used values
  gcongr

theorem every_prefix_with_input_list {α : Type*} (used addressWidth payloadBits : ℕ) (values : List α) :
    payloadBits+addressWidth*(2*values.length+2*((advance used (values,#[])).2.size+1)) ≤
      payloadBits+addressWidth*(4*values.length+2) := by
  have h := every_prefix_table_size used values
  exact Nat.add_le_add_left (Nat.mul_le_mul_left addressWidth (by omega)) payloadBits

end Blotto.ReferenceArrayBuilder
