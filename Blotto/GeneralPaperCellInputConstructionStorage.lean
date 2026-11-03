import Blotto.GeneralPaperNativeNatFillStorage

/-! Actual unsigned projected extras, signed positions and signed extras.
Closed native counters, both reserved buffers, header/index arithmetic and
all source arrays coexist. The unsigned branch retains its intermediate
projection separately; primitive scratch uses the actual complete price. -/
namespace Blotto.GeneralPaperCellInputConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem unsigned_element {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hs : ∀ r,summary.read r<2*U) (ho : ∀ r,options.read r<U) (i : Fin (n+m)) :
    (GeneralPaperUnsignedCellInputPrice.element model.rat W U summary options i).1≤2*U := by
  have h := GeneralPaperUnsignedCellInputPrice.codes true (fun w => w) model.rat W U summary options hs ho i
  have h' : (GeneralPaperUnsignedCellInputPrice.element model.rat W U summary options i).1≤U := by
    simpa only [GeneralPaperUnsignedCellInputPrice.run,ite_true,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn] using h
  omega

def projection {n m : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (_options : FixedArrayTable m ℕ) (count : ℕ) : ℕ :=
  if h : count<n then natBits (GeneralPaperCataloguePointExecution.project model.rat W U (summary.read ⟨count,h⟩)).1 else 0

theorem projection_bound {n m : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) (hs : ∀ r,summary.read r<2*U) (count : ℕ) :
    projection model W U summary options count≤natBits (2*U) := by
  unfold projection
  split
  · rename_i h
    rw [GeneralPaperCataloguePointExecution.project_data]
    have hp := GeneralPaperUnsignedPartition.project_bound U _ (hs ⟨count,h⟩)
    exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  · exact Nat.zero_le _

def unsignedWindow {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (count : ℕ) (hc : count≤n+m) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W summary+GeneralPaperEncodedNatArray.footprint W options+
    GeneralPaperNativeNatFillStorage.window W (GeneralPaperUnsignedCellInputPrice.element model.rat W U summary options) count hc+
    GeneralPaperNativeNatFillStorage.header W U n m (n+m) 62 count+projection model W U summary options count+
    GeneralPaperNativeNatFillStorage.record W (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) model.rat W U summary options).1+
    (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) model.rat W U summary options).2+256*W

def unsignedProfile (model : RationalCostModel) (W U n m : ℕ) : ℕ :=
  (n*(natBits (2*U)+W)+32*W)+(m*(natBits U+W)+32*W)+GeneralPaperNativeNatFillStorage.profile W (n+m) (2*U)+
    (17*(GeneralPaperSignedCutOperands.width (n+m) (2*U)+W)+32*W)+natBits (2*U)+
    ((n+m)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width (n+m) (2*U)+96*W)+
    GeneralPaperUnsignedCellInputPrice.profile model.rat W n m U+256*W

theorem unsigned_bounded {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hs : ∀ r,summary.read r<2*U) (ho : ∀ r,options.read r<U) (count : ℕ) (hc : count≤n+m) :
    unsignedWindow model W U summary options count hc≤unsignedProfile model W U n m := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) summary (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hs r).le) 1)
  have hj := GeneralPaperEncodedNatArray.bounded W (natBits U) options (fun r => Nat.add_le_add_left (binaryWordWidth_mono (ho r).le) 1)
  have hf := GeneralPaperNativeNatFillStorage.bounded W (2*U) (GeneralPaperUnsignedCellInputPrice.element model.rat W U summary options)
    (unsigned_element model W U summary options hs ho) count hc
  have hh := GeneralPaperNativeNatFillStorage.header_bound W U n m (n+m) 62 count (by omega) (by omega) hc (by omega)
  have hp := projection_bound model W U summary options hs count
  have hr := GeneralPaperNativeNatFillStorage.record_bound W U 62
    (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) model.rat W U summary options).1
    (fun i => (GeneralPaperUnsignedCellInputPrice.codes true (fun w => w) model.rat W U summary options hs ho i).trans (by omega)) (by omega) rfl
  have hw := GeneralPaperUnsignedCellInputPrice.bit_work model.rat model.monotone W U summary options hs
  unfold unsignedWindow unsignedProfile
  omega

theorem positions_element {n : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hs : ∀ r,summary.read r<U) (i : Fin (2*n)) :
    (GeneralPaperSignedCellPositionsPrice.element model.rat W U summary i).1≤2*U := by
  have h := (GeneralPaperSignedCellPositionsPrice.codes true (fun w => w) model.rat W U summary hs i).le
  simpa only [GeneralPaperSignedCellPositionsPrice.run,ite_true,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn] using h

def positionsWindow {n : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤2*n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W summary+
    GeneralPaperNativeNatFillStorage.window W (GeneralPaperSignedCellPositionsPrice.element model.rat W U summary) count hc+
    GeneralPaperNativeNatFillStorage.header W U n 0 (2*n) 62 count+
    GeneralPaperNativeNatFillStorage.record W (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) model.rat W U summary).1+
    (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) model.rat W U summary).2+256*W

def positionsProfile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  (n*(natBits U+W)+32*W)+GeneralPaperNativeNatFillStorage.profile W (2*n) (2*U)+
    (17*(GeneralPaperSignedCutOperands.width (2*n) (2*U)+W)+32*W)+
    ((2*n)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width (2*n) (2*U)+96*W)+
    GeneralPaperSignedCellPositionsPrice.profile model.rat W n U+256*W

theorem positions_bounded {n : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hs : ∀ r,summary.read r<U) (count : ℕ) (hc : count≤2*n) : positionsWindow model W U summary count hc≤positionsProfile model W U n := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) summary (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hs r).le) 1)
  have hf := GeneralPaperNativeNatFillStorage.bounded W (2*U) (GeneralPaperSignedCellPositionsPrice.element model.rat W U summary)
    (positions_element model W U summary hs) count hc
  have hh := GeneralPaperNativeNatFillStorage.header_bound W U n 0 (2*n) 62 count (by omega) (by omega) hc (by omega)
  have hr := GeneralPaperNativeNatFillStorage.record_bound W U 62
    (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) model.rat W U summary).1
    (fun i => (GeneralPaperSignedCellPositionsPrice.codes true (fun w => w) model.rat W U summary hs i).le) (by omega) rfl
  have hw := GeneralPaperSignedCellPositionsPrice.bit_work model.rat model.monotone W U summary hs
  unfold positionsWindow positionsProfile
  omega

theorem extras_element {m : ℕ} (model : RationalCostModel) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (ho : ∀ r,options.read r<U) (i : Fin (2*m+1)) :
    (GeneralPaperSignedCellExtrasPrice.element model.rat W U (2*m) rfl options i).1≤2*U := by
  have h := GeneralPaperSignedCellExtrasPrice.codes true (fun w => w) model.rat W U options ho i
  simpa only [GeneralPaperSignedCellExtrasPrice.run,ite_true,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn] using h

def extrasWindow {m : ℕ} (model : RationalCostModel) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (count : ℕ) (hc : count≤2*m+1) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W options+
    GeneralPaperNativeNatFillStorage.window W (GeneralPaperSignedCellExtrasPrice.element model.rat W U (2*m) rfl options) count hc+
    GeneralPaperNativeNatFillStorage.header W U m 0 (2*m+1) 66 count+
    GeneralPaperNativeNatFillStorage.record W (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) model.rat W U options).1+
    (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) model.rat W U options).2+256*W

def extrasProfile (model : RationalCostModel) (W U m : ℕ) : ℕ :=
  (m*(natBits U+W)+32*W)+GeneralPaperNativeNatFillStorage.profile W (2*m+1) (2*U)+
    (17*(GeneralPaperSignedCutOperands.width (2*m+1) (2*U)+W)+32*W)+
    ((2*m+1)*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width (2*m+1) (2*U)+96*W)+
    GeneralPaperSignedCellExtrasPrice.profile model.rat W m U+256*W

theorem extras_bounded {m : ℕ} (model : RationalCostModel) (W U : ℕ) (options : FixedArrayTable m ℕ)
    (ho : ∀ r,options.read r<U) (count : ℕ) (hc : count≤2*m+1) : extrasWindow model W U options count hc≤extrasProfile model W U m := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) options (fun r => Nat.add_le_add_left (binaryWordWidth_mono (ho r).le) 1)
  have hf := GeneralPaperNativeNatFillStorage.bounded W (2*U) (GeneralPaperSignedCellExtrasPrice.element model.rat W U (2*m) rfl options)
    (extras_element model W U options ho) count hc
  have hh := GeneralPaperNativeNatFillStorage.header_bound W U m 0 (2*m+1) 66 count (by omega) (by omega) hc (by omega)
  have hr := GeneralPaperNativeNatFillStorage.record_bound W U 66
    (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) model.rat W U options).1
    (GeneralPaperSignedCellExtrasPrice.codes true (fun w => w) model.rat W U options ho) (by omega) rfl
  have hw := GeneralPaperSignedCellExtrasPrice.bit_work model.rat model.monotone W U options ho
  unfold extrasWindow extrasProfile
  omega

end Blotto.GeneralPaperCellInputConstructionStorage
