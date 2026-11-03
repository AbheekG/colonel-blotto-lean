import Blotto.GeneralPaperSourceRowsStorage

/-! Complete postprocessing storage has the source's sharp simultaneous
rate. Primitive scratch is one active operand reservation, with derived
word growth. Scaling and price monotonicity support a joint reference word. -/
namespace Blotto.GeneralPaperSourceRowsStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def storageCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceRowsStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m ((alphabet x).lambda+1) (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceRowsStorage.profile GeneralPaperSourceRowsStorage.codeProfile
      GeneralPaperSourceRowsStorage.peakProfile GeneralPaperSourceRowsStorage.tailProfile
      GeneralPaperSourceRowsStorage.fieldProfile GeneralPaperSourceRowsStorage.rowPeakProfile
      GeneralPaperSourceRowsStorage.rowTailProfile GeneralPaperEncodedRationalRows.tableProfile
      GeneralPaperEncodedRationalRows.rowProfile GeneralPaperRowBudgetStorage.profile
      GeneralPaperRowBudgetStorage.frameProfile GeneralPaperRowBudgetStorage.tailProfile
      GeneralPaperRowBudgetExecution.width GeneralPaperClosedBidStorage.profile
      GeneralPaperCodeDecodeStorage.profile GeneralPaperClosedBidExecution.width
      GeneralPaperDecoderControls.operandWidth GeneralPaperDecoderControls.controlWord
      GeneralPaperSummaryArrayExecution.arrayWord
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem storage_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((storageCertificate C d W hW).fields,(storageCertificate C d W hW).symbols,
      (storageCertificate C d W hW).accuracy)=(1,2,2) := rfl

def returnedCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperEncodedRationalRows.tableProfile (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows x.m (binaryWordWidth (alphabet x).C)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold GeneralPaperEncodedRationalRows.tableProfile GeneralPaperEncodedRationalRows.rowProfile
    source_space⟩

theorem returned_degrees (W : Input → ℕ) (hW : Tight W) :
    ((returnedCertificate W hW).fields,(returnedCertificate W hW).symbols,
      (returnedCertificate W hW).accuracy)=(1,2,2) := rfl

@[fun_prop]
theorem storage_scaling (model : RationalCostModel) (T m t : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperSourceRowsStorage.profile model W T m t a) := by
  unfold GeneralPaperSourceRowsStorage.profile GeneralPaperSourceRowsStorage.codeProfile
    GeneralPaperSourceRowsStorage.peakProfile GeneralPaperSourceRowsStorage.tailProfile
    GeneralPaperSourceRowsStorage.fieldProfile GeneralPaperSourceRowsStorage.rowPeakProfile
    GeneralPaperSourceRowsStorage.rowTailProfile GeneralPaperEncodedRationalRows.tableProfile
    GeneralPaperEncodedRationalRows.rowProfile GeneralPaperRowBudgetStorage.profile
    GeneralPaperRowBudgetStorage.frameProfile GeneralPaperRowBudgetStorage.tailProfile
    GeneralPaperRowBudgetExecution.width GeneralPaperClosedBidStorage.profile
    GeneralPaperCodeDecodeStorage.profile GeneralPaperClosedBidExecution.width
    GeneralPaperDecoderControls.operandWidth GeneralPaperDecoderControls.controlWord
    GeneralPaperSummaryArrayExecution.arrayWord
  fun_prop

@[fun_prop]
theorem returned_scaling (T m s : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperEncodedRationalRows.tableProfile W T m s) := by
  unfold GeneralPaperEncodedRationalRows.tableProfile GeneralPaperEncodedRationalRows.rowProfile
  fun_prop

theorem storage_mono (actual majorant : RationalCostModel) (h : ∀ w,actual.rat w≤majorant.rat w)
    (W T m t : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) :
    GeneralPaperSourceRowsStorage.profile actual W T m t a≤GeneralPaperSourceRowsStorage.profile majorant W T m t a := by
  unfold GeneralPaperSourceRowsStorage.profile GeneralPaperSourceRowsStorage.peakProfile
    GeneralPaperSourceRowsStorage.tailProfile GeneralPaperSourceRowsStorage.fieldProfile
    GeneralPaperSourceRowsStorage.rowPeakProfile GeneralPaperSourceRowsStorage.rowTailProfile
    GeneralPaperClosedBidStorage.profile GeneralPaperCodeDecodeStorage.profile
    GeneralPaperRowBudgetStorage.profile GeneralPaperRowBudgetStorage.tailProfile
  gcongr <;> apply h

theorem soft_small {r f : Input → ℕ} (hf : Soft r f) (hr : Small r) : Small f := by
  rcases hf with ⟨A,e,hA⟩
  have hl : Small logSize := of_tight (show Tight logSize from ⟨1,fun x => by omega⟩)
  apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => A*r x*(logSize x)^e)
  · fun_prop
  · exact hA

end Blotto.GeneralPaperSourceRowsStorageRates
