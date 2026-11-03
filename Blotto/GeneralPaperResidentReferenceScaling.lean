import Blotto.GeneralPaperSourceReferenceScaling

/-! Compositional positive reference-width scaling of retained resident, input and preparation-space
profile. Every lemma unfolds one existing profile and uses kernel-checked
scaling rules for its immediate children. No phase-space or growth oracle
and no additional algorithm pass is introduced. -/
namespace Blotto
open GeneralPaperReferenceScaling
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace GeneralPaperPrecallResidentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperClassifierResultStorage
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_inputProfile (m k Qv B Hc Hr : ℕ) :
    Scale (fun W => inputProfile W m k Qv B Hc Hr) := by
  fun_prop [inputProfile]
end GeneralPaperPrecallResidentStorage

namespace GeneralPaperClassifierResultStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
@[fun_prop]
theorem reference_scale_profile (m k : ℕ) :
    Scale (fun W => profile W m k) := by
  fun_prop [profile]
end GeneralPaperClassifierResultStorage

namespace GeneralPaperClassifierResultStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
@[fun_prop]
theorem reference_scale_frontProfile (m k : ℕ) :
    Scale (fun W => frontProfile W m k) := by
  fun_prop [frontProfile]
end GeneralPaperClassifierResultStorage

namespace GeneralPaperPreparationCacheStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSourcePreparationSizes
open GeneralPaperScoreScaleParameters
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperPreparationCacheStorage

namespace GeneralPaperMaterializedCacheStorage
@[fun_prop]
theorem reference_scale_powerProfile (m lambda k Qv : ℕ) :
    Scale (fun W => powerProfile W m lambda k Qv) := by
  fun_prop [powerProfile]
end GeneralPaperMaterializedCacheStorage

namespace GeneralPaperMaterializedCacheStorage
@[fun_prop]
theorem reference_scale_gridProfile (m lambda k Qv : ℕ) :
    Scale (fun W => gridProfile W m lambda k Qv) := by
  fun_prop [gridProfile]
end GeneralPaperMaterializedCacheStorage

namespace GeneralPaperPreparationResidentStorage
open GeneralPaperSourcePreparationSizes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
@[fun_prop]
theorem reference_scale_residentProfile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => residentProfile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [residentProfile]
end GeneralPaperPreparationResidentStorage

namespace GeneralPaperPrecallResidentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperClassifierResultStorage
open GeneralPaperCodeAlphabet
@[fun_prop]
theorem reference_scale_residentProfile {m : ℕ} (k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Scale (fun W => residentProfile (m := m) W k Qv a weights Bc Br) := by
  fun_prop [residentProfile]
end GeneralPaperPrecallResidentStorage

namespace GeneralPaperProxyQuotientPrice
@[fun_prop]
theorem reference_scale_word (c : GeneralPaperPrecallCachePrice.Cache) :
    Scale (fun W => word W c) := by
  fun_prop [word]
end GeneralPaperProxyQuotientPrice

namespace GeneralPaperProxyLocationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperQuotientConstructionStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (c : GeneralPaperPrecallCachePrice.Cache) (B : ℕ) :
    Scale (fun W => profile model W c B) := by
  dsimp only [profile]
  fun_prop
end GeneralPaperProxyLocationStorage

namespace GeneralPaperSelectionConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperSelectionStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (Q B : ℕ) :
    Scale (fun W => profile model W Q B) := by
  fun_prop [profile]
end GeneralPaperSelectionConstructionStorage

namespace GeneralPaperClassifierConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperPrecallCacheStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m k B : ℕ) :
    Scale (fun W => profile model W m k B) := by
  fun_prop [profile]
end GeneralPaperClassifierConstructionStorage

namespace GeneralPaperParameterTemporaryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperScoreScaleParameters
open GeneralPaperPreparationCacheStorage
@[fun_prop]
theorem reference_scale_profile (m lambda k Qv : ℕ) :
    Scale (fun W => profile W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperParameterTemporaryStorage

namespace GeneralPaperPowerConstructionStorage
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable
open GeneralPaperEncodedPreparedPowers GeneralPaperEncodedScalarStorage
@[fun_prop]
theorem reference_scale_profile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => profile model W m lambda k Qv) := by
  fun_prop [profile]
end GeneralPaperPowerConstructionStorage

namespace GeneralPaperPreparationResidentStorage
open GeneralPaperSourcePreparationSizes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
@[fun_prop]
theorem reference_scale_ceilingProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => ceilingProfile model W m lambda k Qv) := by
  fun_prop [ceilingProfile]
end GeneralPaperPreparationResidentStorage

namespace GeneralPaperPreparationResidentStorage
open GeneralPaperSourcePreparationSizes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
@[fun_prop]
theorem reference_scale_dyadicProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => dyadicProfile model W m lambda k Qv) := by
  fun_prop [dyadicProfile]
end GeneralPaperPreparationResidentStorage

namespace GeneralPaperPreparationResidentStorage
open GeneralPaperSourcePreparationSizes
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared
@[fun_prop]
theorem reference_scale_constructionProfile (model : RationalCostModel) (m lambda k Qv : ℕ) :
    Scale (fun W => constructionProfile model W m lambda k Qv) := by
  fun_prop [constructionProfile]
end GeneralPaperPreparationResidentStorage

end Blotto
