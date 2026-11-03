import Blotto.GeneralPaperRankRecordConstructionStorage

/-! Actual shifted CDF cuts, projected signed positions and cell
representatives. Every native closed-counter record, reserved buffer,
header and current value is counted, including empty arrays. -/
namespace Blotto.GeneralPaperRankCutArrayStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def core {n : ℕ} (W U scale : ℕ) (callback : Fin n → ℕ × ℕ) (value : FixedArrayTable n ℕ × ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperNativeNatFillStorage.window W callback count hc+
    GeneralPaperNativeNatFillStorage.header W U n 0 n scale count+
    GeneralPaperNativeNatFillStorage.record W value+256*W

def coreProfile (W U n : ℕ) : ℕ :=
  GeneralPaperNativeNatFillStorage.profile W n (2*U)+17*(GeneralPaperSignedCutOperands.width n (2*U)+W)+32*W+
    (n*(natBits (2*U)+W)+GeneralPaperSignedCutOperands.width n (2*U)+96*W)+256*W

theorem core_bound {n : ℕ} (W U scale : ℕ) (callback : Fin n → ℕ × ℕ) (value : FixedArrayTable n ℕ × ℕ)
    (hcallback : ∀ i,(callback i).1≤2*U) (hs : scale≤66)
    (ha : value.1=(PaperIndexedArrayConstruction.run (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W n) callback).1)
    (hw : value.2=scale*n+18) (count : ℕ) (hc : count≤n) : core W U scale callback value count hc≤coreProfile W U n := by
  have hf := GeneralPaperNativeNatFillStorage.bounded W (2*U) callback hcallback count hc
  have hh := GeneralPaperNativeNatFillStorage.header_bound W U n 0 n scale count (Nat.le_refl _) (Nat.zero_le _) hc hs
  have hr := GeneralPaperNativeNatFillStorage.record_bound W U scale value (by
    intro i
    rw [ha,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact hcallback i) hs hw
  unfold core coreProfile
  omega

def shiftWindow {n : ℕ} (model : RationalCostModel) (W shift : ℕ) (queries : FixedArrayTable n ℕ)
    (U count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W queries+
    core W U 54 (GeneralPaperCDFShiftPrice.element model.rat W shift queries)
      (GeneralPaperCDFShiftPrice.run true (fun w => w) model.rat W shift queries).1 count hc+
    fields W [shift]+(GeneralPaperCDFShiftPrice.run true (fun w => w) model.rat W shift queries).2

def shiftProfile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  (n*(natBits U+W)+32*W)+coreProfile W U n+(natBits 1+W+32*W)+GeneralPaperCDFShiftPrice.profile model.rat W n U

theorem shift_bound {n : ℕ} (model : RationalCostModel) (W U shift : ℕ) (queries : FixedArrayTable n ℕ)
    (hs : shift≤1) (hq : ∀ i,queries.read i<U) (count : ℕ) (hc : count≤n) :
    shiftWindow model W shift queries U count hc≤shiftProfile model W U n := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits U) queries (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hq i).le) 1)
  have hcore := core_bound W U 54 (GeneralPaperCDFShiftPrice.element model.rat W shift queries)
    (GeneralPaperCDFShiftPrice.run true (fun w => w) model.rat W shift queries).1 (by
      intro i
      change queries.read i+shift≤2*U
      have h := hq i
      omega) (by omega) rfl rfl count hc
  have hf := fields_bound W (natBits 1) [shift] (by
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact Nat.add_le_add_left (binaryWordWidth_mono hs) 1)
  change fields W [shift]≤1*(natBits 1+W)+32*W at hf
  simp only [Nat.one_mul] at hf
  have hp := GeneralPaperCDFShiftPrice.bit_work model.rat model.monotone W U shift queries hs hq
  unfold shiftWindow shiftProfile
  omega

def projectedWindow {n : ℕ} (model : RationalCostModel) (W U : ℕ) (codes : FixedArrayTable n ℕ)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W codes+
    core W U 58 (GeneralPaperSignedPositionsPrice.element model.rat W U codes)
      (GeneralPaperSignedPositionsPrice.run true (fun w => w) model.rat W U codes).1 count hc+
    (GeneralPaperSignedPositionsPrice.run true (fun w => w) model.rat W U codes).2

def projectedProfile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  (n*(natBits (2*U)+W)+32*W)+coreProfile W U n+GeneralPaperSignedPositionsPrice.profile model.rat W n U

theorem projected_bound {n : ℕ} (model : RationalCostModel) (W U : ℕ) (codes : FixedArrayTable n ℕ)
    (hv : ∀ i,codes.read i<2*U) (count : ℕ) (hc : count≤n) :
    projectedWindow model W U codes count hc≤projectedProfile model W U n := by
  have hi := GeneralPaperEncodedNatArray.bounded W (natBits (2*U)) codes (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hv i).le) 1)
  have hcore := core_bound W U 58 (GeneralPaperSignedPositionsPrice.element model.rat W U codes)
    (GeneralPaperSignedPositionsPrice.run true (fun w => w) model.rat W U codes).1 (by
      intro i
      change (GeneralPaperCataloguePointExecution.project model.rat W U (codes.read i)).1≤2*U
      rw [GeneralPaperCataloguePointExecution.project_data]
      have h := GeneralPaperUnsignedPartition.project_bound U _ (hv i)
      omega) (by omega) rfl rfl count hc
  have hp := GeneralPaperSignedPositionsPrice.bit_work model.rat model.monotone W U codes hv
  unfold projectedWindow projectedProfile
  omega

def representativeWindow {n : ℕ} (model : RationalCostModel) (W U : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n)
    (count : ℕ) (hc : count≤n) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedPartitionStorage.pairBits W) cells+
    core W U 50 (fun i : Fin n => ((cells.read i).1,16*W))
      (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W cells).1 count hc+
    (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W cells).2

def representativeProfile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  (n*(2*natBits U+9*W)+32*W)+coreProfile W U n+GeneralPaperCellRepresentativePrice.profile model.rat W n

theorem representative_bound {n : ℕ} (model : RationalCostModel) (W U : ℕ) (cells : GeneralPaperEpochCellInstructions.Cells n)
    (hv : ∀ i,(cells.read i).1<(cells.read i).2 ∧ (cells.read i).2≤U) (count : ℕ) (hc : count≤n) :
    representativeWindow model W U cells count hc≤representativeProfile model W U n := by
  have hi := GeneralPaperEncodedFixedVector.bounded W (2*natBits U+8*W) (GeneralPaperEncodedPartitionStorage.pairBits W) cells (by
    intro i
    have h := hv i
    have hl := Nat.add_le_add_left (binaryWordWidth_mono (h.1.le.trans h.2)) 1
    have hu := Nat.add_le_add_left (binaryWordWidth_mono h.2) 1
    unfold GeneralPaperEncodedPartitionStorage.pairBits natBits
    omega)
  have hi' : GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedPartitionStorage.pairBits W) cells≤
      n*(2*natBits U+9*W)+32*W := hi.trans_eq (by ring)
  have hcore := core_bound W U 50 (fun i : Fin n => ((cells.read i).1,16*W))
    (GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W cells).1
    (fun i => (hv i).1.le.trans ((hv i).2.trans (by omega))) (by omega) rfl rfl count hc
  have hp := GeneralPaperCellRepresentativePrice.bit_work model.rat model.monotone W cells
  unfold representativeWindow representativeProfile
  omega

end Blotto.GeneralPaperRankCutArrayStorage
