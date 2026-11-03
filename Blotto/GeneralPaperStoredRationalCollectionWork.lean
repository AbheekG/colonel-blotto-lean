import Blotto.GeneralPaperStoredCountReadWork

/-! Actual counted rational-array collection has a sum-of-payload bound.
Native ownership can discharge the extent premise; all reads and counts
refer to the same enclosing installed memory and its count contract. -/
namespace Blotto.GeneralPaperStoredRationalCollectionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory ofArray)
open GeneralPaperRetainedScalarValue (Scalar)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def perElement (model : RationalCostModel) (A : ℕ) : ℕ :=
  GeneralPaperStoredScalarReadWork.overhead model A + GeneralPaperStoredStreamWork.stepBound model A + 128 * (A + 1)

def bound {n : ℕ} (model : RationalCostModel) (A : ℕ) (source : FixedArrayTable n ℚ) : ℕ :=
  3 * (source.data.toList.map rationalWordWidth).sum + n * perElement model A +
    GeneralPaperStoredCountReadWork.bound model A + 192 * (A + 1)

theorem work {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (source : FixedArrayTable n ℚ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))))
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference)
    (hCount : n < 2 ^ A) :
    (GeneralPaperStoredReadStream.rationals model A installed).work ≤ bound model A source := by
  have hCountWork := GeneralPaperStoredCountReadWork.work model A installed full hContract _ hHeader (by change (64 : ℕ) ≠ 0; decide)
  rw [← hRoot] at hCountWork
  have hPrice := GeneralPaperStoredStreamWork.rational_price model S A start installed source hRead hRoot hCount
  rw [(GeneralPaperStoredReadStreamSources.rational_array model S A start installed full hContract source hRead hHeader hRoot).2.2]
  unfold bound perElement
  omega

theorem work_from_owner {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (full : Directory A)
    (hContract : Contract model A installed full) (source : FixedArrayTable n ℚ)
    (hRead : Readback model A installed (ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))))
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference)
    (hA : 0 < A)
    (hOwner : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.stop < 2 ^ A) :
    (GeneralPaperStoredReadStream.rationals model A installed).work ≤ bound model A source :=
  work model S A start installed full hContract source hRead hHeader hRoot
    (by have h := GeneralPaperStoredStreamWork.rational_array_capacity model S A start source hA hOwner; omega)

end Blotto.GeneralPaperStoredRationalCollectionWork
