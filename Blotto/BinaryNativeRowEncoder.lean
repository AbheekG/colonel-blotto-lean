import Blotto.BinaryNativeRationalEncoder
import Blotto.RationalPRGBinaryOutput

/-! Complete row serialization consumes already materialized native rationals.
The cached dimension header and each actual returned suffix are forwarded once.
Array extraction and row production remain separate from these source prices. -/
namespace Blotto.BinaryNativeRowEncoder
set_option autoImplicit false

def list : List ℚ → List Bool → List Bool
  | [],suffix => suffix
  | q::rest,suffix => BinaryNativeRationalEncoder.into q (list rest suffix)

theorem list_data (values : List ℚ) (suffix : List Bool) : list values suffix = BinaryRatListFrame.encode values++suffix := by
  induction values with
  | nil => rfl
  | cons q rest ih =>
      simp only [list,BinaryNativeRationalEncoder.into_data,ih,BinaryRatListFrame.encode,List.flatMap_cons,List.append_assoc]

def frame (header : List Bool) (values : List ℚ) : List Bool :=
  BinaryLinearRowFrame.copyInto header (list values [])

theorem frame_data (header : List Bool) (values : List ℚ) : frame header values = header++BinaryRatListFrame.encode values := by
  simp only [frame,BinaryLinearRowFrame.copy_data,list_data,List.append_nil]

theorem frame_read (values : List ℚ) (suffix : List Bool) :
    BinaryRatListFrame.readRow (frame (BinaryNatFrame.encode values.length) values++suffix) =
      some (values.length,values,suffix) := by
  simp only [frame_data,List.append_assoc,BinaryRatListFrame.readRow,BinaryNatFrame.read_encode_append,
    Option.bind_some,BinaryRatListFrame.read_encode_append,Option.map_some]

def listWork (primitive : ℕ → ℕ) : List ℚ → List Bool → ℕ
  | [],_ => 1
  | q::rest,suffix => listWork primitive rest suffix+
      BinaryNativeRationalEncoder.intoWork primitive q (list rest suffix)+3

theorem list_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (values : List ℚ) (suffix : List Bool) (W : ℕ) (hWidth : ∀ q ∈ values, rationalWordWidth q ≤ W) :
    listWork primitive values suffix ≤
      values.length*(1024*(c+1)*(W+1)*(binaryWordWidth (W+2)+1)+3)+1 := by
  induction values with
  | nil => simp only [listWork,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons q rest ih =>
      have hq := hWidth q (by simp)
      have hr := ih (fun v hv => hWidth v (by simp [hv]))
      have hi := BinaryNativeRationalEncoder.into_work_bound primitive c hPrimitive q (list rest suffix)
      have hp := Nat.mul_le_mul
        (Nat.mul_le_mul_left (1024*(c+1)) (Nat.add_le_add_right hq 1))
        (Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hq 2)) 1)
      simp only [listWork,List.length_cons]
      nlinarith only [hr,hi,hp]

def frameWork (primitive : ℕ → ℕ) (header : List Bool) (values : List ℚ) : ℕ :=
  listWork primitive values []+(BinaryLinearRowFrame.copyRun header (list values [])).trace.length+2

theorem frame_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (header : List Bool) (values : List ℚ) (W : ℕ) (hWidth : ∀ q ∈ values, rationalWordWidth q ≤ W) :
    frameWork primitive header values ≤
      3*header.length+values.length*(1024*(c+1)*(W+1)*(binaryWordWidth (W+2)+1)+3)+4 := by
  have hl := list_work_bound primitive c hPrimitive values [] W hWidth
  have hc := (BinaryLinearRowFrame.copy_counts header (list values [])).1
  unfold frameWork
  omega

theorem frame_length (header : List Bool) (values : List ℚ) :
    (frame header values).length = header.length+2*(values.map rationalWordWidth).sum+values.length := by
  rw [frame_data,List.length_append,BinaryRatListFrame.encode_length]
  omega

theorem array_list {n : ℕ} (row : RationalResourceArray n) : row.data.toList = List.ofFn row.allocation := by
  apply List.ext_getElem
  · simp only [Array.length_toList,List.length_ofFn,row.size]
  · intro j hj hk
    simp only [Array.getElem_toList,List.getElem_ofFn,RationalResourceArray.allocation]

def stored (header : List Bool) {n : ℕ} (row : RationalResourceArray n) : List Bool := frame header row.data.toList

theorem stored_data {n : ℕ} (row : RationalResourceArray n) :
    stored (BinaryNatFrame.encode n) row = BinaryRatListFrame.encodeRow row.allocation := by
  simp only [stored,frame_data,array_list,BinaryRatListFrame.encodeRow]

theorem stored_read {n : ℕ} (row : RationalResourceArray n) (suffix : List Bool) :
    BinaryRatListFrame.readRow (stored (BinaryNatFrame.encode n) row++suffix) = some (n,List.ofFn row.allocation,suffix) := by
  rw [stored_data]
  exact BinaryRatListFrame.readRow_encode_append row.allocation suffix

theorem stored_work_bound {n : ℕ} (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (header : List Bool) (row : RationalResourceArray n) (W : ℕ) (hWidth : ∀ j, rationalWordWidth (row.allocation j) ≤ W) :
    frameWork primitive header row.data.toList ≤
      3*header.length+n*(1024*(c+1)*(W+1)*(binaryWordWidth (W+2)+1)+3)+4 := by
  have h := frame_work_bound primitive c hPrimitive header (List.ofFn row.allocation) W
    (by intro q hq; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hWidth j)
  simpa only [array_list,List.length_ofFn] using h

end Blotto.BinaryNativeRowEncoder
