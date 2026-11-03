import Blotto.GeneralPaperAllBranchReferenceCalibration
import Blotto.GeneralPaperNativeReferenceEnlargement

/-! Actual once-only accuracy preparation and measured reference construction
on the shared original rational input. Parsed provenance is retained for the
continuation; no source reserve is evaluated by this initializer. -/
namespace Blotto.GeneralPaperOriginalMeasuredReference
open GeneralPaperOriginalGameInput
open GeneralPaperOriginalReferenceComparison (logarithm)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def prepare (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (GeneralPaperBinaryAccuracy.Parsed × ℕ) × ℕ :=
  let precision := GeneralPaperBinaryAccuracy.prepare id A p.words
  let parsed : GeneralPaperBinaryAccuracy.Parsed :=
    ⟨p.words, precision.1, GeneralPaperBinaryAccuracy.prepare_data id A p.words⟩
  let reference := GeneralPaperEqualReferenceConstruction.measured model A K parsed.exponent p.values p.budget p.words
  ((parsed, reference.1), precision.2 + reference.2 + 64 * A + 64)

theorem words (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).1.1.words = p.words := rfl

theorem exponent (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).1.1.exponent = (equalInput model p).k :=
  GeneralPaperEqualInputInitialization.initialized_exponent model A K (equalInput model p)

theorem word (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).1.2 = K * logarithm model p :=
  GeneralPaperEqualInputInitialization.initialized_word model A K (equalInput model p)

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input) :
    (prepare model A K p).2 ≤
      GeneralPaperEqualInputInitialization.initializationPrice model A K (equalInput model p) :=
  GeneralPaperEqualInputInitialization.initialization_work model A K (equalInput model p)

theorem uniform_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (p : Input) (A : ℕ),
      GeneralPaperStoredPreparationUniformCapacity.envelope model K (equalInput model p) <
        2 ^ (prepare model A K p).1.2 ∧ ∀ h : p.budget < 1,
      GeneralPaperNativeResourceReferenceGrowth.word model C d (unequalInput p h) ≤ (prepare model A K p).1.2 ∧
      GeneralPaperNativeResourceReferenceGrowth.reserve model C d (prepare model A K p).1.2 (unequalInput p h) <
        2 ^ (prepare model A K p).1.2 := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperAllBranchReferenceCalibration.uniform_calibration hg
  refine ⟨K, hK, fun p A => ?_⟩
  rw [word]
  exact ⟨(hSafe p).1, fun h => ⟨(hSafe p).2 h,
    GeneralPaperNativeReferenceEnlargement.reserve_above model C d (unequalInput p h) _ ((hSafe p).2 h)⟩⟩

end Blotto.GeneralPaperOriginalMeasuredReference
