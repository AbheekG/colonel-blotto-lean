import Blotto.GeneralPaperPhysicalShiftStorage

/-! Physical response ownership fits the sharp source space rate. Absorb
field-squared rational-row and scan widths separately before combining them
with the decoder's alphabet-squared term; coarse coordinatewise maxima of
their degree triples would lose an unnecessary alphabet factor. -/
namespace Blotto.GeneralPaperPhysicalResponseStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

def rowCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperEncodedRationalRows.rowProfile (W x) x.m (GeneralPaperPhysicalBidStorage.height x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x))) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold GeneralPaperEncodedRationalRows.rowProfile GeneralPaperPhysicalBidStorage.height
      GeneralPaperResponsePhysicalHeights.bidHeight GeneralPaperResponsePhysicalHeights.shiftHeight
    source_space⟩

theorem row_degrees (W : Input → ℕ) (hW : Tight W) :
    ((rowCertificate W hW).fields,(rowCertificate W hW).symbols,(rowCertificate W hW).accuracy)=(2,1,0) := rfl

theorem row_rate (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperEncodedRationalRows.rowProfile (W x) x.m (GeneralPaperPhysicalBidStorage.height x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x))) 1 2 0 :=
  rate_mono (rowCertificate W hW).bound GeneralPaperSourceRowsRates.field_absorption

def bidCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPhysicalBidStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalBidStorage.profile GeneralPaperCodeDecodeStorage.profile
      GeneralPaperClosedBidExecution.width GeneralPaperDecoderControls.operandWidth GeneralPaperDecoderControls.controlWord
      GeneralPaperPhysicalBidExecution.additionWidth GeneralPaperResponsePhysicalHeights.word
      GeneralPaperResponsePhysicalHeights.prefixHeight GeneralPaperResponsePhysicalHeights.bidHeight
      GeneralPaperResponsePhysicalHeights.shiftHeight
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem bid_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((bidCertificate C d W hW).fields,(bidCertificate C d W hW).symbols,(bidCertificate C d W hW).accuracy)=(1,2,0) := rfl

def budgetCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperRowBudgetStorage.profile (GeneralPaperFastRationalMajorant.model C d) (arrayWord (W x) x.m) x.m
      (GeneralPaperPhysicalBidStorage.height x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x))
      ((alphabet x).lambda+1)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperRowBudgetStorage.profile GeneralPaperRowBudgetStorage.frameProfile GeneralPaperRowBudgetStorage.tailProfile
      GeneralPaperRowBudgetExecution.width GeneralPaperPhysicalBidStorage.height
      GeneralPaperResponsePhysicalHeights.bidHeight GeneralPaperResponsePhysicalHeights.shiftHeight arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem budget_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((budgetCertificate C d W hW).fields,(budgetCertificate C d W hW).symbols,(budgetCertificate C d W hW).accuracy)=(2,1,0) := rfl

theorem budget_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperRowBudgetStorage.profile (GeneralPaperFastRationalMajorant.model C d) (arrayWord (W x) x.m) x.m
      (GeneralPaperPhysicalBidStorage.height x.m (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x))
      ((alphabet x).lambda+1)) 1 2 0 :=
  rate_mono (budgetCertificate C d W hW).bound GeneralPaperSourceRowsRates.field_absorption

def storageCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPhysicalResponseStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  have hRow := row_rate W hW
  have hBid := (bidCertificate C d W hW).bound
  have hBudget := budget_rate C d W hW
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalResponseStorage.profile GeneralPaperPhysicalResponseStorage.rowPeakProfile
      GeneralPaperPhysicalResponseStorage.rowTailProfile GeneralPaperRowBudgetStorage.frameProfile
      GeneralPaperDecoderControls.operandWidth GeneralPaperResponsePhysicalHeights.shiftHeight arrayWord
    source_space⟩

theorem storage_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((storageCertificate C d W hW).fields,(storageCertificate C d W hW).symbols,(storageCertificate C d W hW).accuracy)=(1,2,0) := rfl

def shiftCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperPhysicalShiftStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m
      (GeneralPaperProxyParameters.prepare x.m x.k).qbar (alphabet x).C) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperPhysicalShiftStorage.profile GeneralPaperPhysicalShiftStorage.powerPayload
      GeneralPaperPhysicalShiftExecution.width GeneralPaperPhysicalShiftExecution.natWidth arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem shift_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((shiftCertificate C d W hW).fields,(shiftCertificate C d W hW).symbols,(shiftCertificate C d W hW).accuracy)=(1,1,0) := rfl

@[fun_prop]
theorem scaling (model : RationalCostModel) (m qbar t : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperPhysicalResponseStorage.profile model W m qbar t a) := by
  unfold GeneralPaperPhysicalResponseStorage.profile GeneralPaperPhysicalResponseStorage.rowPeakProfile
    GeneralPaperPhysicalResponseStorage.rowTailProfile GeneralPaperEncodedRationalRows.rowProfile
    GeneralPaperPhysicalBidStorage.profile GeneralPaperCodeDecodeStorage.profile GeneralPaperDecoderControls.controlWord
    GeneralPaperRowBudgetStorage.profile GeneralPaperRowBudgetStorage.frameProfile GeneralPaperRowBudgetStorage.tailProfile arrayWord
  fun_prop

@[fun_prop]
theorem shift_scaling (model : RationalCostModel) (m qbar C : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperPhysicalShiftStorage.profile model W m qbar C) := by
  unfold GeneralPaperPhysicalShiftStorage.profile arrayWord
  fun_prop

theorem monotone_profile (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W m qbar t : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperPhysicalResponseStorage.profile actual W m qbar t a≤
      GeneralPaperPhysicalResponseStorage.profile majorant W m qbar t a := by
  unfold GeneralPaperPhysicalResponseStorage.profile GeneralPaperPhysicalResponseStorage.rowPeakProfile
    GeneralPaperPhysicalResponseStorage.rowTailProfile GeneralPaperPhysicalBidStorage.profile GeneralPaperCodeDecodeStorage.profile
    GeneralPaperRowBudgetStorage.profile GeneralPaperRowBudgetStorage.tailProfile
  gcongr <;> apply h

theorem shift_monotone (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W m qbar C : ℕ) : GeneralPaperPhysicalShiftStorage.profile actual W m qbar C≤
      GeneralPaperPhysicalShiftStorage.profile majorant W m qbar C := by
  unfold GeneralPaperPhysicalShiftStorage.profile
  dsimp only
  gcongr
  apply h

end Blotto.GeneralPaperPhysicalResponseStorageRates
