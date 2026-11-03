import Blotto.GeneralPaperIntegerDotStorage

/-! Actual native integer matrix/vector materialization: full reserved
output buffers and returned vector, callback/outer counters and one active
dot window. Original matrix/vector owners are retained once by the caller.
Literal next-column extraction uses the same checked indexed fill. -/
namespace Blotto.GeneralPaperBasisProductStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits)
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 8192

def callbackPrice (model : RationalCostModel) (W n R : ℕ) : ℕ := 128*(n+1)*(W+model.rat R)+4*W
def callbackCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+1+3*callbackPrice model W n R+4*W
def callbackWindow {n : ℕ} (model : RationalCostModel) (W copied : ℕ) (f g : Fin n → Fin n → ℤ) (i : Fin n) : ℕ :=
  let dot := GeneralPaperIntegerDotPrice.run model.rat W (f i) (g i)
  GeneralPaperIntegerDotStorage.window model W copied (f i) (g i)+integerBits dot.value+
    fields W [n,i.val,dot.work,dot.work+4*W,4*W]+128*W
def callbackProfile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperIntegerDotStorage.profile model W n R+R+5*(natBits (callbackCap model W n R)+W)+160*W

theorem result_word {n : ℕ} (model : RationalCostModel) (W X Y R : ℕ) (f g : Fin n → ℤ)
    (hf : ∀ i,(f i).natAbs≤X) (hg : ∀ i,(g i).natAbs≤Y)
    (hR : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y)≤R) :
    integerBits (GeneralPaperIntegerDotPrice.run model.rat W f g).value≤R := by
  have h : (GeneralPaperIntegerDotPrice.run model.rat W f g).value.natAbs≤n*X*Y := by
    rw [GeneralPaperIntegerDotPrice.data]; exact GeneralPaperIntegerDotSize.run_bound f g X Y hf hg
  exact (Nat.add_le_add_left (binaryWordWidth_mono (h.trans (GeneralPaperIntegerDotPrice.cap_bounds n X Y).2.2)) 1).trans hR

theorem callback_bound {n : ℕ} (model : RationalCostModel) (W copied X Y R : ℕ) (f g : Fin n → Fin n → ℤ)
    (hf : ∀ i j,(f i j).natAbs≤X) (hg : ∀ i j,(g i j).natAbs≤Y)
    (hR : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y)≤R) (i : Fin n) :
    callbackWindow model W copied f g i≤callbackProfile model W n R := by
  let dot := GeneralPaperIntegerDotPrice.run model.rat W (f i) (g i)
  have hDot := GeneralPaperIntegerDotStorage.bounded model W copied X Y R (f i) (g i) (hf i) (hg i) hR
  have hValue := result_word model W X Y R (f i) (g i) (hf i) (hg i) hR
  have hWork := (GeneralPaperIntegerDotPrice.work model.rat model.monotone W X Y (f i) (g i) (hf i) (hg i)).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change dot.work≤128*(n+1)*(W+model.rat R) at hWork
  have hf' := fields_bound W (natBits (callbackCap model W n R)) [n,i.val,dot.work,dot.work+4*W,4*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold callbackCap callbackPrice; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (callbackCap model W n R)+W)+32*W at hf'
  unfold callbackWindow callbackProfile
  dsimp only
  dsimp only [dot] at hf'
  omega

def callerCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+1+3*GeneralPaperNativePayloadFillStorage.workCap W n (callbackPrice model W n R)+4*W
def window {n : ℕ} (model : RationalCostModel) (W copied : ℕ) (f g : Fin n → Fin n → ℤ) : ℕ :=
  let callback := fun i => let dot := GeneralPaperIntegerDotPrice.run model.rat W (f i) (g i); (dot.value,dot.work+4*W)
  let result := GeneralPaperBasisProductBits.materialize model.rat W f g
  GeneralPaperNativePayloadFillStorage.window W integerBits callback (callbackWindow model W copied f g)
    (min copied n) (Nat.min_le_right _ _)+fields W [n,result.2,4*W]+128*W
def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W R n (callbackPrice model W n R) (callbackProfile model W n R)+
    3*(natBits (callerCap model W n R)+W)+160*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W copied X Y R : ℕ) (f g : Fin n → Fin n → ℤ)
    (hf : ∀ i j,(f i j).natAbs≤X) (hg : ∀ i j,(g i j).natAbs≤Y)
    (hR : 1+binaryWordWidth (GeneralPaperIntegerDotPrice.cap n X Y)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+1)≤W) : window model W copied f g≤profile model W n R := by
  let callback := fun i => let dot := GeneralPaperIntegerDotPrice.run model.rat W (f i) (g i); (dot.value,dot.work+4*W)
  have hC (i) : (callback i).2≤callbackPrice model W n R := Nat.add_le_add_right
    ((GeneralPaperIntegerDotPrice.work model.rat model.monotone W X Y (f i) (g i) (hf i) (hg i)).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))) (4*W)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (callbackPrice model W n R) (callbackProfile model W n R)
    integerBits callback (callbackWindow model W copied f g)
    (fun i => result_word model W X Y R (f i) (g i) (hf i) (hg i) hR) hC
    (callback_bound model W copied X Y R f g hf hg hR) hW hIndex (min copied n) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (callbackPrice model W n R) callback hC hW hIndex n le_rfl
  change (GeneralPaperBasisProductBits.materialize model.rat W f g).2≤GeneralPaperNativePayloadFillStorage.workCap W n (callbackPrice model W n R) at hWork
  have hf' := fields_bound W (natBits (callerCap model W n R)) [n,(GeneralPaperBasisProductBits.materialize model.rat W f g).2,4*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (callerCap model W n R)+W)+32*W at hf'
  unfold window profile
  dsimp only
  dsimp only [callback] at hFill
  omega

def columnCap (W j d : ℕ) : ℕ := j+d+1+3*GeneralPaperNativePayloadFillStorage.workCap W j (8*W)+8*W
def columnWindow {j d : ℕ} (W copied : ℕ) (rows : Rows j d) (next : Fin d) : ℕ :=
  let result := GeneralPaperBasisAssemblyBits.columnRun W rows next
  GeneralPaperNativePayloadFillStorage.window W integerBits (fun i => ((rows.read i).coefficients.read next,8*W)) (fun _ => 0)
    (min copied j) (Nat.min_le_right _ _)+fields W [j,d,next.val,result.2,8*W]+128*W
def columnProfile (W j d R : ℕ) : ℕ := GeneralPaperNativePayloadFillStorage.profile W R j (8*W) 0+
  5*(natBits (columnCap W j d)+W)+160*W

theorem column_bound {j d : ℕ} (W copied C R : ℕ) (rows : Rows j d) (next : Fin d)
    (hr : ∀ i k,((rows.read i).coefficients.read k).natAbs≤C) (hR : 1+binaryWordWidth C≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (j+1)≤W) : columnWindow W copied rows next≤columnProfile W j d R := by
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (8*W) 0 integerBits
    (fun i => ((rows.read i).coefficients.read next,8*W)) (fun _ => 0)
    (fun i => (Nat.add_le_add_left (binaryWordWidth_mono (hr i next)) 1).trans hR) (fun _ => le_rfl) (fun _ => le_rfl)
    hW hIndex (min copied j) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (8*W)
    (fun i => ((rows.read i).coefficients.read next,8*W)) (fun _ => le_rfl) hW hIndex j le_rfl
  change (GeneralPaperBasisAssemblyBits.columnRun W rows next).2≤GeneralPaperNativePayloadFillStorage.workCap W j (8*W) at hWork
  have hf' := fields_bound W (natBits (columnCap W j d)) [j,d,next.val,(GeneralPaperBasisAssemblyBits.columnRun W rows next).2,8*W] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold columnCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (columnCap W j d)+W)+32*W at hf'
  unfold columnWindow columnProfile
  dsimp only
  omega

end Blotto.GeneralPaperBasisProductStorage
