import Blotto.GeneralPaperRayQueryStorageRates

/-! A uniform operand envelope for the complete local ray-query phase
profile. R bounds actual words and heights; it is erased analysis, never a
runtime input or oracle. The envelope keeps native metadata logarithmic. -/
namespace Blotto.GeneralPaperRayQueryStorageEnvelope
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedScoreMatrixStorage GeneralPaperScoreConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192

def frameProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  8*(natBits (m+K+S+1+GeneralPaperRayMinimumBits.profile m K S W (model.rat R))+W)+32*W+(1+2*R)+256*W

def costProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  5*R+4*model.rat R+entryProfile W S R+
    10*(natBits (m+K+S+1+32*W+4*model.rat R)+W)+32*W+256*W

def constructionProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  matrixProfile W m K S R+fieldProfile W K S R+
    constructorProfile W m (256*(m+1)*(K+1)*(W+model.rat R))+
    constructorProfile W K (128*(K+1)*(W+model.rat R))+
    costProfile model W m K S R+m*(2*W)+32*W+
    7*(natBits (m+K+S+1+128*(K+1)*(W+model.rat R)+256*(m+1)*(K+1)*(W+model.rat R)+
      512*(m+1)*(K+1)*(W+model.rat R)+(8*m+4)*W)+W)+32*W+256*W

def minimumProfile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  matrixProfile W m K S R+m*(2*W)+32*W+GeneralPaperHighMinimumStorage.profile model W K S R m+
    6*(natBits (m+K+S+1+GeneralPaperRayMinimumBits.profile m K S W (model.rat R))+W)+32*W+256*W

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  frameProfile model W m K S R+constructionProfile model W m K S R+
    (matrixProfile W m K S R+m*(2*W)+32*W+256*W)+
    GeneralPaperScoreLifetimeStorage.callerProfile model W K S R m+GeneralPaperScoreInitialStorage.profile W K S+
    GeneralPaperScoreLifetimeStorage.layerProfile model W K S R m+minimumProfile model W m K S R

theorem dominates (model : RationalCostModel) (W m K S D M R : ℕ)
    (hR : GeneralPaperCommonLatticeDPBits.width D M m≤R) :
    GeneralPaperRayQueryStorage.profile model W m K S D M≤profile model W m K S R := by
  have hA := (GeneralPaperRayQueryStorageRates.height_le_width D M m).trans hR
  unfold GeneralPaperRayQueryStorage.profile GeneralPaperRayQueryStorage.frameProfile GeneralPaperRayQueryStorage.residentProfile
    GeneralPaperRayFieldConstructionStorage.profile GeneralPaperRayFieldConstructionStorage.metadataCap
    GeneralPaperRayFieldConstructionStorage.fieldPrice GeneralPaperRayFieldConstructionStorage.matrixPrice GeneralPaperRayFieldConstructionStorage.fieldsPrice
    GeneralPaperRayCostStorage.profile GeneralPaperRayCostStorage.metadataCap
    GeneralPaperRayMinimumStorage.profile GeneralPaperRayMinimumStorage.metadataCap GeneralPaperRayMinimumStorage.price
    profile frameProfile constructionProfile costProfile minimumProfile
    GeneralPaperRayMinimumBits.profile GeneralPaperHighMinimumStorage.profile GeneralPaperHighMinimumStorage.metadataCap GeneralPaperHighMinimumStorage.workCap
    GeneralPaperIndexedMinimumStorage.profile GeneralPaperIndexedMinimumStorage.frameProfile GeneralPaperIndexedMinimumStorage.workCap
    GeneralPaperScoreLifetimeStorage.layerProfile GeneralPaperScoreLifetimeStorage.callerProfile GeneralPaperScoreLifetimeStorage.workCap
    GeneralPaperScoreConstructionStorage.stepProfile GeneralPaperScoreConstructionStorage.constructorProfile
    GeneralPaperScoreScanStorage.profile GeneralPaperScoreScanStorage.frameProfile GeneralPaperScoreScanStorage.workCap
    GeneralPaperScoreInitialStorage.profile GeneralPaperEncodedScoreMatrixStorage.matrixProfile GeneralPaperEncodedScoreMatrixStorage.fieldProfile
    GeneralPaperEncodedScoreMatrixStorage.entryProfile GeneralPaperScoreTableStorage.tableProfile GeneralPaperScoreSelectionStorage.optionProfile
    GeneralPaperScoreSelectionStorage.selectionProfile GeneralPaperCommonLatticeMinimumBits.profile GeneralPaperScoreDPBits.profile
    GeneralPaperScoreDPBits.stepProfile GeneralPaperScoreDPBits.initialProfile GeneralPaperScoreBitPrimitive.resourceWidth
    GeneralPaperEncodedScalarStorage.natBits
  unfold GeneralPaperScoreConstructionStorage.constructorProfile GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  gcongr <;> first | exact hA | exact hR | (apply model.monotone; gcongr)

end Blotto.GeneralPaperRayQueryStorageEnvelope
