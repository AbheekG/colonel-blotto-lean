import Blotto.GeneralPaperSourceMatrixStorage

/-! Full literal matrix-construction storage has the paper source rate.
Argument/quotient scratch and all entry, constructor and physical-wrapper
work counters are included. The actual model is bounded by its proved fast
majorant only in analysis; no execution, heights or source calls change. -/
namespace Blotto.GeneralPaperScoreEntryStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCompilerReferenceGrowth GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem depth_tight : Tight (fun x => (GeneralPaperScoreScaleParameters.prepare x.m x.k).depth) := by
  have h : Tight (fun x => binaryWordWidth (x.m*(GeneralPaperProxyParameters.prepare x.m x.k).K)+1) := by fun_prop
  rcases h with ⟨C,hC⟩
  exact ⟨C,fun x => (GeneralPaperScoreScaleParameters.depth_bound x.m x.k).trans (hC x)⟩

@[fun_prop]
theorem depth_rate : Rated (fun x => (GeneralPaperScoreScaleParameters.prepare x.m x.k).depth) 0 0 0 :=
  poly (poly_tight _ depth_tight)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperSourceMatrixStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperSourceMatrixStorage.sourceProfile GeneralPaperSourceMatrixStorage.profile
      GeneralPaperSourceMatrixStorage.metadataCap GeneralPaperSourceMatrixStorage.physicalPrice
      GeneralPaperScoreMatrixEntryStorage.profile GeneralPaperScoreMatrixConstructionStorage.profile
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperScoreEntryStorage.profile GeneralPaperScoreEntryStorage.metadataCap
      GeneralPaperScoreArgumentStorage.profile GeneralPaperBitQuotientStorage.profile
      GeneralPaperBitQuotientStorage.counterFrameProfile GeneralPaperBitQuotientStorage.metadataCap
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
      GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperSummaryArrayExecution.arrayWord
    unfold GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(1,1,1) := rfl

theorem profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceMatrixStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv) 1 1 1 :=
  (certificate C d W hW).bound

theorem scaling (model : RationalCostModel) (m k Qv : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperSourceMatrixStorage.sourceProfile model W m k Qv) := by
  unfold GeneralPaperSourceMatrixStorage.sourceProfile GeneralPaperSourceMatrixStorage.profile
      GeneralPaperSourceMatrixStorage.metadataCap GeneralPaperSourceMatrixStorage.physicalPrice
      GeneralPaperScoreMatrixEntryStorage.profile GeneralPaperScoreMatrixConstructionStorage.profile
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperScoreEntryStorage.profile GeneralPaperScoreEntryStorage.metadataCap
      GeneralPaperScoreArgumentStorage.profile GeneralPaperBitQuotientStorage.profile
      GeneralPaperBitQuotientStorage.counterFrameProfile GeneralPaperBitQuotientStorage.metadataCap
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
      GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperSummaryArrayExecution.arrayWord
  unfold GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

theorem profile_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k Qv : ℕ) :
    GeneralPaperSourceMatrixStorage.sourceProfile actual W m k Qv≤GeneralPaperSourceMatrixStorage.sourceProfile upper W m k Qv := by
  unfold GeneralPaperSourceMatrixStorage.sourceProfile GeneralPaperSourceMatrixStorage.profile
      GeneralPaperSourceMatrixStorage.metadataCap GeneralPaperSourceMatrixStorage.physicalPrice
      GeneralPaperScoreMatrixEntryStorage.profile GeneralPaperScoreMatrixConstructionStorage.profile
      GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScoreMatrixStorage.matrixProfile
      GeneralPaperEncodedScoreMatrixStorage.fieldProfile GeneralPaperEncodedScoreMatrixStorage.entryProfile
      GeneralPaperScoreEntryStorage.profile GeneralPaperScoreEntryStorage.metadataCap
      GeneralPaperScoreArgumentStorage.profile GeneralPaperBitQuotientStorage.profile
      GeneralPaperBitQuotientStorage.counterFrameProfile GeneralPaperBitQuotientStorage.metadataCap
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperScoreMatrixBits.matrixProfile GeneralPaperScoreMatrixBits.fieldProfile
      GeneralPaperScoreMatrixBits.entryProfile GeneralPaperScoreMatrixBits.scoreProfile
      GeneralPaperScoreArgumentBits.argumentProfile GeneralPaperScoreArgumentBits.height
      GeneralPaperBoundedQuotient.bitProfile GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperEncodedScalarStorage.natBits GeneralPaperSummaryArrayExecution.arrayWord
  dsimp only
  gcongr <;> exact h _

theorem actual_profile_rate {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : Input → ℕ) (hW : Tight W) : Rated (fun x =>
    GeneralPaperSourceMatrixStorage.sourceProfile actual (W x) x.m x.k x.Qv) 1 1 1 :=
  GeneralPaperSourceSoftBounds.dominated (profile_rate C d W hW)
    (fun x => profile_mono actual (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k x.Qv)

theorem at_one_small (C d : ℕ) : Small (fun x =>
    GeneralPaperSourceMatrixStorage.sourceProfile (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k x.Qv) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (profile_rate C d (fun _ => 1) (tight_constant 1))
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word_bound {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) : ∃ A e : ℕ,∀ x,
    GeneralPaperSourceMatrixStorage.sourceProfile actual (GeneralPaperCompilerReference.width C d x) x.m x.k x.Qv≤
      A*monomial 1 1 1 x*(logSize x)^e := actual_profile_rate hg _ (width_tight C d)

end Blotto.GeneralPaperScoreEntryStorageRates

