import Blotto.GeneralPaperSourceBasisCacheStorageReachedRates

/-! Literal native prefix extraction and retained-row reference append.
The checked fills own complete capacity/return buffers, payload references,
native frames and one active read/branch callback. Original dense-row and
basis owners are retained once by the enclosing advance window. -/
namespace Blotto.GeneralPaperBasisArrayStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisDenseRow GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile rowFootprint)
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def callbackCap (W j d : ℕ) : ℕ := j+d+2+8*W
def callbackWindow (W j d p i : ℕ) : ℕ := fields W [j,d,i,p]+128*W
def callbackProfile (W j d : ℕ) : ℕ := 4*(natBits (callbackCap W j d)+W)+160*W

theorem callback_bound (W j d p i : ℕ) (hp : p≤8*W) (hi : i≤j+1) :
    callbackWindow W j d p i≤callbackProfile W j d := by
  have hf := fields_bound W (natBits (callbackCap W j d)) [j,d,i,p] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold callbackCap
    rcases ha with rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (callbackCap W j d)+W)+32*W at hf
  unfold callbackWindow callbackProfile
  omega

def prefixCap (W j d : ℕ) : ℕ := j+d+2+3*GeneralPaperNativePayloadFillStorage.workCap W j (4*W)+8*W
def prefixWindow {j d : ℕ} (W copied : ℕ) (row : Dense d) (hj : j≤d) : ℕ :=
  let callback := fun i : Fin j => (row.coefficients.read (GeneralPaperBasisPrefixSum.embed hj i),4*W)
  let result := GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W row hj
  GeneralPaperNativePayloadFillStorage.window W integerBits callback (fun i => callbackWindow W j d (4*W) i.val)
    (min copied j) (Nat.min_le_right _ _)+fields W [j,d,result.2,4*W]+128*W
def prefixProfile (W j d R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W R j (4*W) (callbackProfile W j d)+4*(natBits (prefixCap W j d)+W)+160*W

theorem prefix_bound {j d : ℕ} (W copied R : ℕ) (row : Dense d) (hj : j≤d)
    (hr : ∀ i,integerBits (row.coefficients.read i)≤R) (hW : 1≤W) (hJ : binaryWordWidth (j+1)≤W) :
    prefixWindow W copied row hj≤prefixProfile W j d R := by
  let callback := fun i : Fin j => (row.coefficients.read (GeneralPaperBasisPrefixSum.embed hj i),4*W)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (4*W) (callbackProfile W j d) integerBits callback
    (fun i => callbackWindow W j d (4*W) i.val) (fun i => hr _) (fun _ => le_rfl)
    (fun i => callback_bound W j d (4*W) i.val (by omega) (by omega)) hW hJ (min copied j) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (4*W) callback (fun _ => le_rfl) hW hJ j le_rfl
  change (GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W row hj).2≤GeneralPaperNativePayloadFillStorage.workCap W j (4*W) at hWork
  have hf := fields_bound W (natBits (prefixCap W j d)) [j,d,(GeneralPaperBasisArrayPrice.prefixRun (fun w => w) W row hj).2,4*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold prefixCap
    rcases ha with rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (prefixCap W j d)+W)+32*W at hf
  unfold prefixWindow prefixProfile
  dsimp only
  dsimp only [callback] at hFill
  omega

def appendCap (W j d : ℕ) : ℕ := j+d+2+3*GeneralPaperNativePayloadFillStorage.workCap W (j+1) (8*W)+8*W
def appendWindow {j d : ℕ} (W copied : ℕ) (rows : Rows j d) (new : Dense d) : ℕ :=
  let callback := fun i : Fin (j+1) => (if h : i.val<j then rows.read ⟨i.val,h⟩ else new,8*W)
  let result := GeneralPaperBasisArrayPrice.appendRun (fun w => w) W rows new
  GeneralPaperNativePayloadFillStorage.window W (rowFootprint W) callback (fun i => callbackWindow W j d (8*W) i.val)
    (min copied (j+1)) (Nat.min_le_right _ _)+fields W [j,d,result.2,8*W]+128*W
def appendProfile (W j d P : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W P (j+1) (8*W) (callbackProfile W j d)+4*(natBits (appendCap W j d)+W)+160*W

theorem append_bound {j d : ℕ} (W copied P : ℕ) (rows : Rows j d) (new : Dense d)
    (hRows : ∀ i,rowFootprint W (rows.read i)≤P) (hNew : rowFootprint W new≤P)
    (hW : 1≤W) (hJ : binaryWordWidth (j+2)≤W) : appendWindow W copied rows new≤appendProfile W j d P := by
  let callback := fun i : Fin (j+1) => (if h : i.val<j then rows.read ⟨i.val,h⟩ else new,8*W)
  have hp (i : Fin (j+1)) : rowFootprint W (callback i).1≤P := by dsimp only [callback]; split; exact hRows _; exact hNew
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W P (8*W) (callbackProfile W j d) (rowFootprint W) callback
    (fun i => callbackWindow W j d (8*W) i.val) hp (fun _ => le_rfl)
    (fun i => callback_bound W j d (8*W) i.val le_rfl (by omega)) hW hJ (min copied (j+1)) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (8*W) callback (fun _ => le_rfl) hW hJ (j+1) le_rfl
  change (GeneralPaperBasisArrayPrice.appendRun (fun w => w) W rows new).2≤GeneralPaperNativePayloadFillStorage.workCap W (j+1) (8*W) at hWork
  have hf := fields_bound W (natBits (appendCap W j d)) [j,d,(GeneralPaperBasisArrayPrice.appendRun (fun w => w) W rows new).2,8*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    unfold appendCap
    rcases ha with rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (appendCap W j d)+W)+32*W at hf
  unfold appendWindow appendProfile
  dsimp only
  dsimp only [callback] at hFill
  omega

end Blotto.GeneralPaperBasisArrayStorage
