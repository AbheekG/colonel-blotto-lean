import Blotto.GeneralPaperRayQueryStorage
import Blotto.GeneralPaperGuardMinimumStorageRates
import Blotto.GeneralPaperRayQueryWidth

/-! Positive reference scaling, model domination and soft growth for every
local native ray-query phase together. Height and common-word families are
erased analytical premises. Actual reachable source-state instantiation and
outer query owners still have to be joined. -/
namespace Blotto.GeneralPaperRayQueryStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

theorem height_le_width (D M m : ℕ) : GeneralPaperRayMinimumStorage.height D M≤
    GeneralPaperCommonLatticeDPBits.width D M m := by
  have hM := binaryWordWidth_mono (show M+1≤(m+1)*M+1 by nlinarith only [Nat.zero_le (m*M)])
  unfold GeneralPaperRayMinimumStorage.height GeneralPaperCommonLatticeDPBits.width
  omega

theorem operand_height {m D E X V P s : ℕ} (t : ℚ) (ht : RationalHeight t s) :
    GeneralPaperRayMinimumStorage.height (D*t.den) (X+V+1)≤
      1+2*(GeneralPaperRayUniformSize.width D E m X V P+s) :=
  (height_le_width _ _ m).trans (GeneralPaperRayQueryWidth.width (E:=E) (P:=P) t ht)

theorem scaling (model : RationalCostModel) (m K S D M : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperRayQueryStorage.profile model W m K S D M) := by
  unfold GeneralPaperRayQueryStorage.profile GeneralPaperRayQueryStorage.frameProfile GeneralPaperRayQueryStorage.residentProfile
      GeneralPaperRayFieldConstructionStorage.profile GeneralPaperRayFieldConstructionStorage.metadataCap
      GeneralPaperRayFieldConstructionStorage.fieldPrice GeneralPaperRayFieldConstructionStorage.matrixPrice GeneralPaperRayFieldConstructionStorage.fieldsPrice
      GeneralPaperRayCostStorage.profile GeneralPaperRayCostStorage.metadataCap
      GeneralPaperRayMinimumStorage.profile GeneralPaperRayMinimumStorage.metadataCap GeneralPaperRayMinimumStorage.price
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m K S D M : ℕ) :
    GeneralPaperRayQueryStorage.profile actual W m K S D M≤GeneralPaperRayQueryStorage.profile upper W m K S D M := by
  unfold GeneralPaperRayQueryStorage.profile GeneralPaperRayQueryStorage.frameProfile GeneralPaperRayQueryStorage.residentProfile
      GeneralPaperRayFieldConstructionStorage.profile GeneralPaperRayFieldConstructionStorage.metadataCap
      GeneralPaperRayFieldConstructionStorage.fieldPrice GeneralPaperRayFieldConstructionStorage.matrixPrice GeneralPaperRayFieldConstructionStorage.fieldsPrice
      GeneralPaperRayCostStorage.profile GeneralPaperRayCostStorage.metadataCap
      GeneralPaperRayMinimumStorage.profile GeneralPaperRayMinimumStorage.metadataCap GeneralPaperRayMinimumStorage.price
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> exact h _

def certificate (C d : ℕ) (W D M : Input → ℕ) (hW : Tight W)
    (hA : Rated (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)) 1 1 1)
    (hsA : Small (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)))
    (hP : Rated (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m) 1 1 1)
    (hsP : Small (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m)) :
    Certificate (fun x => GeneralPaperRayQueryStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperProxyParameters.prepare x.m x.k).S (D x) (M x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperRayQueryStorage.profile GeneralPaperRayQueryStorage.frameProfile GeneralPaperRayQueryStorage.residentProfile
      GeneralPaperRayFieldConstructionStorage.profile GeneralPaperRayFieldConstructionStorage.metadataCap
      GeneralPaperRayFieldConstructionStorage.fieldPrice GeneralPaperRayFieldConstructionStorage.matrixPrice GeneralPaperRayFieldConstructionStorage.fieldsPrice
      GeneralPaperRayCostStorage.profile GeneralPaperRayCostStorage.metadataCap
      GeneralPaperRayMinimumStorage.profile GeneralPaperRayMinimumStorage.metadataCap GeneralPaperRayMinimumStorage.price
      GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
      GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
      GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
      GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
      GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
      GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
      GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
      GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
      GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth GeneralPaperEncodedScalarStorage.natBits
    unfold GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W D M : Input → ℕ) (hW : Tight W)
    (hA : Rated (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)) 1 1 1)
    (hsA : Small (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)))
    (hP : Rated (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m) 1 1 1)
    (hsP : Small (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m)) :
    ((certificate C d W D M hW hA hsA hP hsP).fields,(certificate C d W D M hW hA hsA hP hsP).symbols,
      (certificate C d W D M hW hA hsA hP hsP).accuracy)=(3,1,2) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W D M : Input → ℕ) (hW : Tight W)
    (hA : Rated (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)) 1 1 1)
    (hsA : Small (fun x => GeneralPaperRayMinimumStorage.height (D x) (M x)))
    (hP : Rated (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m) 1 1 1)
    (hsP : Small (fun x => GeneralPaperCommonLatticeDPBits.width (D x) (M x) x.m)) : Rated (fun x =>
    GeneralPaperRayQueryStorage.profile actual (W x) x.m (GeneralPaperProxyParameters.prepare x.m x.k).K
      (GeneralPaperProxyParameters.prepare x.m x.k).S (D x) (M x)) 3 1 2 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W D M hW hA hsA hP hsP).bound
    (fun x => model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg)
      (W x) x.m _ _ (D x) (M x))

end Blotto.GeneralPaperRayQueryStorageRates

