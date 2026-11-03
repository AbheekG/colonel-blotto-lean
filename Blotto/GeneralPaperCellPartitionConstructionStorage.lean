import Blotto.GeneralPaperEpochPartitionConstructionStorage

/-! Full unsigned/signed native field partitions. Actual constructed arrays
derive every endpoint cap; all input-array, breakpoint-list, ordered-partition,
native return, caller metadata and scratch phases coexist conservatively. -/
namespace Blotto.GeneralPaperCellPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def unsignedExtras {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :=
  (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) model.rat W U summary options).1.1

def signedPositions {n : ℕ} (model : RationalCostModel) (W U : ℕ) (summary : FixedArrayTable n ℕ) :=
  (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) model.rat W U summary).1.1

def signedExtras {m : ℕ} (model : RationalCostModel) (W U : ℕ) (options : FixedArrayTable m ℕ) :=
  (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) model.rat W U options).1.1

theorem unsigned_returned {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary signedSummary options).1≤
      GeneralPaperEncodedPartitionStorage.profile W (natBits U) (2*n+(n+m)+1) :=
  GeneralPaperEpochPartitionConstructionStorage.returned model W U cdfSummary (unsignedExtras model W U signedSummary options)

def unsignedWindow {n m : ℕ} (model : RationalCostModel) (W U inputCount usedP usedE copied count : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (hi : inputCount≤n+m)
    (hc : count≤(GeneralPaperEpochPartition.prepare U cdfSummary (unsignedExtras model W U signedSummary options)).count) : ℕ :=
  GeneralPaperCellInputConstructionStorage.unsignedWindow model W U signedSummary options inputCount hi+
    GeneralPaperEpochPartitionConstructionStorage.window model W U usedP usedE copied count cdfSummary
      (unsignedExtras model W U signedSummary options) hc+
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary signedSummary options).1+
    fields W [U,n,m]+(GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary signedSummary options).2+256*W

def unsignedProfile (model : RationalCostModel) (W U n m : ℕ) : ℕ :=
  GeneralPaperCellInputConstructionStorage.unsignedProfile model W U n m+
    GeneralPaperEpochPartitionConstructionStorage.profile model W U n (n+m)+
    GeneralPaperEncodedPartitionStorage.profile W (natBits U) (2*n+(n+m)+1)+fields W [U,n,m]+
    GeneralPaperUnsignedCellPartitionPrice.profile model.rat W n m U+256*W

theorem unsigned_bounded {n m : ℕ} (model : RationalCostModel) (W U inputCount usedP usedE copied count : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ r,cdfSummary.read r<U) (hs : ∀ r,signedSummary.read r<2*U) (ho : ∀ r,options.read r<U)
    (hi : inputCount≤n+m)
    (hc : count≤(GeneralPaperEpochPartition.prepare U cdfSummary (unsignedExtras model W U signedSummary options)).count) :
    unsignedWindow model W U inputCount usedP usedE copied count cdfSummary signedSummary options hi hc≤unsignedProfile model W U n m := by
  have hinput := GeneralPaperCellInputConstructionStorage.unsigned_bounded model W U signedSummary options hs ho inputCount hi
  have hpart := GeneralPaperEpochPartitionConstructionStorage.bounded model W U usedP usedE copied count cdfSummary
    (unsignedExtras model W U signedSummary options) hCDF
    (GeneralPaperUnsignedCellInputPrice.codes true (fun w => w) model.rat W U signedSummary options hs ho) hc
  have hr := unsigned_returned model W U cdfSummary signedSummary options
  have hw := GeneralPaperUnsignedCellPartitionPrice.bit_work model.rat model.monotone W U cdfSummary signedSummary options hCDF hs ho
  unfold unsignedWindow unsignedProfile
  omega

theorem signed_returned {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).1≤
      GeneralPaperEncodedPartitionStorage.profile W (natBits (2*U)) (2*(2*n)+(2*m+1)+1) :=
  GeneralPaperEpochPartitionConstructionStorage.returned model W (2*U) (signedPositions model W U summary) (signedExtras model W U options)

def signedWindow {n m : ℕ} (model : RationalCostModel) (W U positionCount extraCount usedP usedE copied count : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (hp : positionCount≤2*n) (he : extraCount≤2*m+1)
    (hc : count≤(GeneralPaperEpochPartition.prepare (2*U) (signedPositions model W U summary) (signedExtras model W U options)).count) : ℕ :=
  GeneralPaperCellInputConstructionStorage.positionsWindow model W U summary positionCount hp+
    GeneralPaperCellInputConstructionStorage.extrasWindow model W U options extraCount he+
    GeneralPaperEpochPartitionConstructionStorage.window model W (2*U) usedP usedE copied count
      (signedPositions model W U summary) (signedExtras model W U options) hc+
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).1+
    fields W [U,2*U,n,m]+(GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).2+256*W

def signedProfile (model : RationalCostModel) (W U n m : ℕ) : ℕ :=
  GeneralPaperCellInputConstructionStorage.positionsProfile model W U n+GeneralPaperCellInputConstructionStorage.extrasProfile model W U m+
    GeneralPaperEpochPartitionConstructionStorage.profile model W (2*U) (2*n) (2*m+1)+
    GeneralPaperEncodedPartitionStorage.profile W (natBits (2*U)) (2*(2*n)+(2*m+1)+1)+fields W [U,2*U,n,m]+
    GeneralPaperSignedCellPartitionPrice.profile model.rat W n m U+256*W

theorem signed_bounded {n m : ℕ} (model : RationalCostModel) (W U positionCount extraCount usedP usedE copied count : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) (hs : ∀ r,summary.read r<U) (ho : ∀ r,options.read r<U)
    (hp : positionCount≤2*n) (he : extraCount≤2*m+1)
    (hc : count≤(GeneralPaperEpochPartition.prepare (2*U) (signedPositions model W U summary) (signedExtras model W U options)).count) :
    signedWindow model W U positionCount extraCount usedP usedE copied count summary options hp he hc≤signedProfile model W U n m := by
  have hpositions := GeneralPaperCellInputConstructionStorage.positions_bounded model W U summary hs positionCount hp
  have hextras := GeneralPaperCellInputConstructionStorage.extras_bounded model W U options ho extraCount he
  have hpart := GeneralPaperEpochPartitionConstructionStorage.bounded model W (2*U) usedP usedE copied count
    (signedPositions model W U summary) (signedExtras model W U options)
    (GeneralPaperSignedCellPositionsPrice.codes true (fun w => w) model.rat W U summary hs)
    (GeneralPaperSignedCellExtrasPrice.codes true (fun w => w) model.rat W U options ho) hc
  have hr := signed_returned model W U summary options
  have hw := GeneralPaperSignedCellPartitionPrice.bit_work model.rat model.monotone W U summary options hs ho
  unfold signedWindow signedProfile
  omega

end Blotto.GeneralPaperCellPartitionConstructionStorage
