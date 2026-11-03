import Blotto.PaperIndexedArrayConstruction
import Blotto.ReferenceArrayBuilder

/-! Sequential list materialization in the paper's mutable-reference-array
model. Each step reads one cons cell and appends one reference to a buffer
whose final capacity is known. The old buffer is not retained by the source
schedule. Prices reuse the indexed constructor's control/write primitives;
they assert no native allocator, persistent-copy or reference-count rate.
-/
namespace Blotto.PaperListReferenceArray
set_option autoImplicit false
set_option maxHeartbeats 2000000

def into {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) : List α → Array α → Array α × ℕ
  | [],data => (data,0)
  | x::rest,data =>
    let step := PaperIndexedArrayConstruction.stepWork primitive W data.size+8*W
    let later := into primitive W rest (data.push x)
    (later.1,later.2+step)

theorem into_data {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) (xs : List α) (data : Array α) :
    (into primitive W xs data).1=ReferenceArrayBuilder.into xs data := by
  induction xs generalizing data with
  | nil => rfl
  | cons x rest ih => exact ih (data.push x)

theorem into_size {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) (xs : List α) (data : Array α) :
    (into primitive W xs data).1.size=data.size+xs.length := by
  rw [into_data,ReferenceArrayBuilder.into_size]

def run {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) (xs : List α) : Array α × ℕ :=
  let result := into primitive W xs #[]
  (result.1,result.2+PaperIndexedArrayConstruction.initialWork primitive W xs.length+(8*xs.length+8)*W)

theorem data {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) (xs : List α) :
    (run primitive W xs).1=xs.toArray := by
  change (into primitive W xs #[]).1=xs.toArray
  rw [into_data]
  exact ReferenceArrayBuilder.array_data xs

theorem size {α : Type*} (primitive : ℕ → ℕ) (W : ℕ) (xs : List α) :
    (run primitive W xs).1.size=xs.length := by rw [data,List.size_toArray]

theorem into_work {α : Type*} (primitive : ℕ → ℕ) (W cap E : ℕ) (xs : List α) (data : Array α)
    (hCap : data.size+xs.length≤cap)
    (hStep : ∀ i≤cap,PaperIndexedArrayConstruction.stepWork primitive W i+8*W≤E) :
    (into primitive W xs data).2≤xs.length*E := by
  induction xs generalizing data with
  | nil => simp only [into,List.length_nil,Nat.zero_mul,le_refl]
  | cons x rest ih =>
    have hc : (data.push x).size+rest.length≤cap := by
      simp only [Array.size_push,List.length_cons] at hCap ⊢
      omega
    have hr := ih (data.push x) hc
    have hs := hStep data.size (by simp only [List.length_cons] at hCap; omega)
    change (into primitive W rest (data.push x)).2+
      (PaperIndexedArrayConstruction.stepWork primitive W data.size+8*W)≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem bit_work {α : Type*} (W : ℕ) (xs : List α) (hW : 1≤W)
    (hIndex : binaryWordWidth (xs.length+1)≤W) :
    (run (fun w => w) W xs).2≤64*(xs.length+1)*W := by
  have hr := into_work (fun w => w) W xs.length (50*W) xs #[] (by simp)
    (by
      intro i hi
      have hw := (binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans hIndex
      unfold PaperIndexedArrayConstruction.stepWork
      dsimp only
      omega)
  change (into (fun w => w) W xs #[]).2+
    PaperIndexedArrayConstruction.initialWork (fun w => w) W xs.length+(8*xs.length+8)*W≤_
  unfold PaperIndexedArrayConstruction.initialWork
  nlinarith only [hr,hW,hIndex]

theorem arithmetic_work {α : Type*} (xs : List α) :
    (run (fun _ => 1) 1 xs).2≤64*(xs.length+1) := by
  have hr := into_work (fun _ => 1) 1 xs.length 50 xs #[] (by simp)
    (by intro i _; simp only [PaperIndexedArrayConstruction.stepWork]; omega)
  change (into (fun _ => 1) 1 xs #[]).2+
    PaperIndexedArrayConstruction.initialWork (fun _ => 1) 1 xs.length+(8*xs.length+8)*1≤_
  unfold PaperIndexedArrayConstruction.initialWork
  nlinarith only [hr]

theorem every_prefix_capacity {α : Type*} (used : ℕ) (xs : List α) :
    (ReferenceArrayBuilder.advance used (xs,#[])).2.size≤xs.length :=
  ReferenceArrayBuilder.every_prefix_table_size used xs

theorem every_prefix_with_input_references {α : Type*} (used W payloadBits : ℕ) (xs : List α) :
    payloadBits+W*(2*xs.length+2*(ReferenceArrayBuilder.advance used (xs,#[])).2.size+1)≤
      payloadBits+W*(4*xs.length+1) := by
  have hh := every_prefix_capacity used xs
  exact Nat.add_le_add_left (Nat.mul_le_mul_left W (by omega)) payloadBits

end Blotto.PaperListReferenceArray
