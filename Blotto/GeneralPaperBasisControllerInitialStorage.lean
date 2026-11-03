import Blotto.GeneralPaperSourceEndpointScalarStorageReachedRates

/-! Literal zero-stage basis initialization. Both zero-length native
array constructors retain their complete capacity/fill/return headers and
frames. The complete empty basis, determinant one and all seven parent
partial-work fields are retained. This is not grid/control preparation. -/
namespace Blotto.GeneralPaperBasisControllerInitialStorage
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisOriginalDirection
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (footprint rowFootprint arrayFootprint integerBits)
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def rowsCallback (d : ℕ) : Fin 0 → GeneralPaperBasisDenseRow.Dense d×ℕ := fun i => (Fin.elim0 i,0)
def adjCallback : Fin 0 → Vector 0×ℕ := fun i => (Fin.elim0 i,0)
def controls (W d : ℕ) : List ℕ :=
  let rows := PaperIndexedArrayConstruction.run (fun w => w) W (rowsCallback d)
  let adj := PaperIndexedArrayConstruction.run (fun w => w) W adjCallback
  let empty := GeneralPaperBasisArrayPrice.initialRun (fun w => w) W d
  [d,rows.2,adj.2,empty.2,empty.2+8*W,8*W,rows.2+adj.2]
def window (W d : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.window W (rowFootprint W) (rowsCallback d) (fun i => Fin.elim0 i) 0 le_rfl+
    GeneralPaperNativePayloadFillStorage.window W (arrayFootprint W integerBits) adjCallback (fun i => Fin.elim0 i) 0 le_rfl+
    footprint W (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W d).1+fields W (controls W d)+128*W
def metadataCap (W d : ℕ) : ℕ := d+1+128*W
def profile (W d : ℕ) : ℕ :=
  2*GeneralPaperNativePayloadFillStorage.profile W 0 0 0 0+160*W+2+
    7*(natBits (metadataCap W d)+W)+160*W

theorem empty_basis (W d : ℕ) : footprint W (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W d).1=160*W+2 := by
  rw [GeneralPaperBasisArrayPrice.initial_data]
  simp only [footprint,arrayFootprint,Fin.sum_univ_zero,Nat.add_zero,GeneralPaperBasisState.initial,GeneralPaperBasisStoredCorrect.initial]
  have hOne : integerBits (1:ℤ)=2 := by decide
  change 64*W+integerBits (1:ℤ)+64*W+32*W=160*W+2
  rw [hOne]
  omega

theorem bounded (W d : ℕ) (hW : 1≤W) : window W d≤profile W d := by
  have hIndex : binaryWordWidth (0+1)≤W := by
    have h : binaryWordWidth (0+1)=1 := by decide
    omega
  have hRows := GeneralPaperNativePayloadFillStorage.bounded W 0 0 0 (rowFootprint W) (rowsCallback d) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hW hIndex 0 le_rfl
  have hAdj := GeneralPaperNativePayloadFillStorage.bounded W 0 0 0 (arrayFootprint W integerBits) adjCallback (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) hW hIndex 0 le_rfl
  have hState := empty_basis W d
  have hEmpty := GeneralPaperBasisAppendBits.initial_work W d hW
  have hShape : (GeneralPaperBasisArrayPrice.initialRun (fun w => w) W d).2=
      (PaperIndexedArrayConstruction.run (fun w => w) W (rowsCallback d)).2+
        (PaperIndexedArrayConstruction.run (fun w => w) W adjCallback).2+8*W := rfl
  have hf := fields_bound W (natBits (metadataCap W d)) (controls W d) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls W d)≤7*(natBits (metadataCap W d)+W)+32*W at hf
  unfold window profile
  omega

end Blotto.GeneralPaperBasisControllerInitialStorage
