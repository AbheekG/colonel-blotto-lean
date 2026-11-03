import Blotto.GeneralPaperActualReadyStorage

/-! Reserved storage for the existing indexed natural-array constructor.
Native callers prove their callback values; no observer executes in the
algorithm and primitive scratch is joined by the callers' actual prices. -/
namespace Blotto.GeneralPaperNativeNatFillStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def filledPrefix {n : ℕ} (W : ℕ) (callback : Fin n → ℕ × ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W n natBits
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n) callback count hc).1

theorem prefix_bound {n : ℕ} (W V : ℕ) (callback : Fin n → ℕ × ℕ) (hv : ∀ i,(callback i).1≤V)
    (count : ℕ) (hc : count≤n) : filledPrefix W callback count hc≤n*(natBits V+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n)
    W (natBits V) natBits callback (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i)) 1) count hc

theorem returned {n : ℕ} (W V : ℕ) (callback : Fin n → ℕ × ℕ) (hv : ∀ i,(callback i).1≤V) :
    GeneralPaperEncodedNatArray.footprint W
      (PaperIndexedArrayConstruction.run (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n) callback).1≤
      n*(natBits V+W)+32*W := by
  apply GeneralPaperEncodedNatArray.bounded
  intro i
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact Nat.add_le_add_left (binaryWordWidth_mono (hv i)) 1

def current {n : ℕ} (callback : Fin n → ℕ × ℕ) (count : ℕ) : ℕ :=
  if h : count<n then natBits (callback ⟨count,h⟩).1 else 0

theorem current_bound {n : ℕ} (V : ℕ) (callback : Fin n → ℕ × ℕ) (hv : ∀ i,(callback i).1≤V) (count : ℕ) :
    current callback count≤natBits V := by
  unfold current
  split
  · exact Nat.add_le_add_left (binaryWordWidth_mono (hv _)) 1
  · exact Nat.zero_le _

def window {n : ℕ} (W : ℕ) (callback : Fin n → ℕ × ℕ) (count : ℕ) (hc : count≤n) : ℕ :=
  2*filledPrefix W callback count hc+GeneralPaperGridArrayConstructionStorage.frames W n+
    GeneralPaperEncodedNatArray.footprint W
      (PaperIndexedArrayConstruction.run (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n) callback).1+
    current callback count+fields W [n,count,count+1,n+1]+128*W

def profile (W n V : ℕ) : ℕ :=
  2*(n*(natBits V+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W n+
    (n*(natBits V+W)+32*W)+natBits V+4*(natBits (n+1)+W)+160*W

theorem bounded {n : ℕ} (W V : ℕ) (callback : Fin n → ℕ × ℕ) (hv : ∀ i,(callback i).1≤V)
    (count : ℕ) (hc : count≤n) : window W callback count hc≤profile W n V := by
  have hp := prefix_bound W V callback hv count hc
  have hr := returned W V callback hv
  have hv' := current_bound V callback hv count
  have hf := fields_bound W (natBits (n+1)) [n,count,count+1,n+1] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> unfold natBits <;>
      exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
  change fields W [n,count,count+1,n+1]≤4*(natBits (n+1)+W)+32*W at hf
  unfold window profile
  omega

def header (W U n m total scale count : ℕ) : ℕ :=
  fields W [U,2*U,n,m,2*n,2*m,total,total+1,count,count-n,count-m,scale,scale*total,scale*total+18,18,1,2]

theorem header_bound (W U n m total scale count : ℕ) (hn : n≤total) (hm : m≤total)
    (hc : count≤total) (hs : scale≤66) : header W U n m total scale count≤
      17*(GeneralPaperSignedCutOperands.width total (2*U)+W)+32*W := by
  have hp := Nat.mul_le_mul_right total hs
  apply fields_bound
  intro x hx
  apply (Nat.add_le_add_left (binaryWordWidth_mono (show x≤GeneralPaperSignedCutOperands.magnitude total (2*U) from ?_)) 1).trans
    (GeneralPaperSignedCutOperands.word_bound total (2*U))
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    unfold GeneralPaperSignedCutOperands.magnitude <;> omega

def record {n : ℕ} (W : ℕ) (value : FixedArrayTable n ℕ × ℕ) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W value.1+natBits value.2+64*W

theorem record_bound {n : ℕ} (W U scale : ℕ) (value : FixedArrayTable n ℕ × ℕ)
    (hv : ∀ i,value.1.read i≤2*U) (hs : scale≤66) (ha : value.2=scale*n+18) :
    record W value≤n*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n (2*U)+96*W := by
  have hv' := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) value.1
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i)) 1)
  have hp := Nat.mul_le_mul_right n hs
  have ha' := (Nat.add_le_add_left (binaryWordWidth_mono
    (show value.2≤GeneralPaperSignedCutOperands.magnitude n (2*U) by rw [ha]; unfold GeneralPaperSignedCutOperands.magnitude; omega)) 1).trans
      (GeneralPaperSignedCutOperands.word_bound n (2*U))
  change natBits value.2≤_ at ha'
  unfold record
  omega

end Blotto.GeneralPaperNativeNatFillStorage
