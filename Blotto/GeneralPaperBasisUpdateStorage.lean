import Blotto.GeneralPaperBasisEntryStorage

/-! Two literal native indexed fills materialize the bordered adjugate.
Full row/matrix buffers, returned payloads and native fill frames coexist
with one active scalar/row window. The enclosing cache owns old inputs
once; the row callback does not retain a copy of the old matrix. -/
namespace Blotto.GeneralPaperBasisUpdateStorage
open GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def rowPrice (model : RationalCostModel) (W n R : ℕ) : ℕ := 128*(n+2)*(W+model.rat R)
def rowCap (model : RationalCostModel) (W n R : ℕ) : ℕ := n+2+3*rowPrice model W n R
def rowWindow {n : ℕ} (model : RationalCostModel) (W copied : ℕ) (D Dnext : ℤ)
    (A : IntMatrix n) (au va : Vector n) (j : Fin (n+1)) : ℕ :=
  let callback := GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j
  let result := GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va j
  GeneralPaperNativePayloadFillStorage.window W integerBits callback
    (GeneralPaperBasisEntryStorage.window model W D Dnext A au va j)
    (min copied (n+1)) (Nat.min_le_right _ _)+fields W [n,j.val,result.2]+128*W
def rowProfile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W R (n+1) (GeneralPaperBasisEntryStorage.price model W R)
    (GeneralPaperBasisEntryStorage.profile model W n R)+3*(natBits (rowCap model W n R)+W)+160*W

theorem row_payload {n : ℕ} (model : RationalCostModel) (W H U V L R : ℕ) (D Dnext : ℤ)
    (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k)
    (hR : 1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)≤R) (j : Fin (n+1)) :
    arrayFootprint W integerBits (GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va j).1≤arrayProfile W (n+1) R := by
  apply GeneralPaperEncodedBasisStorage.array_bound
  intro k
  rw [GeneralPaperBasisUpdateBits.rowRun,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperBasisEntryStorage.result_word model W H U V L R D Dnext A au va hD hNext hA hU hV hExact hR j k

theorem row_bound {n : ℕ} (model : RationalCostModel) (W copied H U V L R : ℕ) (D Dnext : ℤ)
    (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k)
    (hR : 1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+2)≤W) (j : Fin (n+1)) :
    rowWindow model W copied D Dnext A au va j≤rowProfile model W n R := by
  have hC (k) : (GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j k).2≤GeneralPaperBasisEntryStorage.price model W R :=
    (GeneralPaperBasisEntryBits.work model.rat model.monotone W H U V L D Dnext A au va hD hNext hA hU hV hExact j k).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 8 (model.monotone hR)) (32*W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W R (GeneralPaperBasisEntryStorage.price model W R)
    (GeneralPaperBasisEntryStorage.profile model W n R) integerBits
    (GeneralPaperBasisEntryBits.run model.rat W D Dnext A au va j)
    (GeneralPaperBasisEntryStorage.window model W D Dnext A au va j)
    (GeneralPaperBasisEntryStorage.result_word model W H U V L R D Dnext A au va hD hNext hA hU hV hExact hR j) hC
    (GeneralPaperBasisEntryStorage.bounded model W H U V L R D Dnext A au va hD hNext hA hU hV hExact hR j)
    hW hIndex (min copied (n+1)) (Nat.min_le_right _ _)
  have hWork := (GeneralPaperBasisUpdateBits.row_work model.rat model.monotone W H U V L hW hIndex D Dnext A au va
    hD hNext hA hU hV hExact j).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  change (GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va j).2≤rowPrice model W n R at hWork
  have hf := fields_bound W (natBits (rowCap model W n R)) [n,j.val,(GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va j).2] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals unfold rowCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (rowCap model W n R)+W)+32*W at hf
  unfold rowWindow rowProfile
  dsimp only
  omega

def callerCap (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  n+2+3*GeneralPaperNativePayloadFillStorage.workCap W (n+1) (rowPrice model W n R)
def window {n : ℕ} (model : RationalCostModel) (W outerCopied innerCopied : ℕ) (D Dnext : ℤ)
    (A : IntMatrix n) (au va : Vector n) : ℕ :=
  let callback := GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va
  let result := GeneralPaperBasisUpdateBits.run model.rat W D Dnext A au va
  GeneralPaperNativePayloadFillStorage.window W (arrayFootprint W integerBits) callback
    (rowWindow model W innerCopied D Dnext A au va) (min outerCopied (n+1)) (Nat.min_le_right _ _)+
    fields W [n,result.2]+128*W
def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W (arrayProfile W (n+1) R) (n+1) (rowPrice model W n R)
    (rowProfile model W n R)+2*(natBits (callerCap model W n R)+W)+160*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W outerCopied innerCopied H U V L R : ℕ) (D Dnext : ℤ)
    (A : IntMatrix n) (au va : Vector n)
    (hD : D.natAbs≤H) (hNext : Dnext.natAbs≤L) (hA : ∀ i k,((A.read i).read k).natAbs≤H)
    (hU : ∀ i,(au.read i).natAbs≤U) (hV : ∀ i,(va.read i).natAbs≤V)
    (hExact : ∀ i k,D∣Dnext*(A.read i).read k+au.read i*va.read k)
    (hR : 1+binaryWordWidth (GeneralPaperBasisEntryBits.cap H U V L)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (n+2)≤W) :
    window model W outerCopied innerCopied D Dnext A au va≤profile model W n R := by
  have hC (j) : (GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va j).2≤rowPrice model W n R :=
    (GeneralPaperBasisUpdateBits.row_work model.rat model.monotone W H U V L hW hIndex D Dnext A au va
      hD hNext hA hU hV hExact j).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left (model.monotone hR) W))
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (arrayProfile W (n+1) R) (rowPrice model W n R)
    (rowProfile model W n R) (arrayFootprint W integerBits) (GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va)
    (rowWindow model W innerCopied D Dnext A au va)
    (row_payload model W H U V L R D Dnext A au va hD hNext hA hU hV hExact hR) hC
    (row_bound model W innerCopied H U V L R D Dnext A au va hD hNext hA hU hV hExact hR hW hIndex)
    hW hIndex (min outerCopied (n+1)) (Nat.min_le_right _ _)
  have hWork := GeneralPaperNativePayloadFillStorage.prefix_work W (rowPrice model W n R)
    (GeneralPaperBasisUpdateBits.rowRun model.rat W D Dnext A au va) hC hW hIndex (n+1) le_rfl
  change (GeneralPaperBasisUpdateBits.run model.rat W D Dnext A au va).2≤GeneralPaperNativePayloadFillStorage.workCap W (n+1) (rowPrice model W n R) at hWork
  have hf := fields_bound W (natBits (callerCap model W n R)) [n,(GeneralPaperBasisUpdateBits.run model.rat W D Dnext A au va).2] (by
    intro a ha; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl
    all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (callerCap model W n R)+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperBasisUpdateStorage
