import Blotto.GeneralPaperCatalogueEpochMetadata

/-! Full-code increment, loss-magnitude and ordered-variation bounds for
the concrete two-optimizer epoch. Its own level cap supplies positivity;
summary ordering/codes enter only the variation argument. No global loss or
increment callbacks are assumed independently of execution.
-/
namespace Blotto.GeneralPaperCatalogueLossBounds
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun GeneralPaperCatalogueOccurrenceHistory
open GeneralPaperCatalogueEpochMetadata GeneralPaperGeometricLevels GeneralPaperOrderedVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem increment_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (code : ℕ) :
    increment learner (selected cache Qv weights Bc Br) time j code≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  have he := GeneralPaperAdaptiveLossBounds.increment_bounds
    (fieldAt (selected cache Qv weights Bc Br) time j) (snapshotAt (selected cache Qv weights Bc Br) time j)
    (choiceAt (selected cache Qv weights Bc Br) time j) (selected_positive cache Qv weights Bc Br time hTime j)
    (snapshot_coherent _ _ _)
  cases learner with
  | p => exact he.1 code
  | q => exact he.2.1 code
  | lambda => exact he.2.2.1 code
  | mu => exact he.2.2.2 code

theorem magnitude_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) (code : ℕ) :
    |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment learner (selected cache Qv weights Bc Br) time j code):ℝ)|≤2 := by
  have he := GeneralPaperAdaptiveLossBounds.magnitudes
    (fieldAt (selected cache Qv weights Bc Br) time j) (snapshotAt (selected cache Qv weights Bc Br) time j)
    (choiceAt (selected cache Qv weights Bc Br) time j) (selected_positive cache Qv weights Bc Br time hTime j)
    (snapshot_coherent _ _ _)
  cases learner with
  | p => exact he.1 code
  | q => exact he.2.1 code
  | lambda => exact (he.2.2.1 code).trans (by norm_num)
  | mu => exact (he.2.2.2 code).trans (by norm_num)

theorem variation_bound {m k : ℕ} (learner : Learner) (cache : Cache m k) (Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hOrdered : Ordered cache) (hCodes : CodesValid cache) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (j : Fin m) :
    variation (fun code => (executedLoss (GeneralPaperSourceParameters.prepare k).theta
      (increment learner (selected cache Qv weights Bc Br) time j code):ℝ)) (width learner cache-1)≤4 := by
  have ho : GeneralPaperEpochFieldPlan.Ordered (fieldAt (selected cache Qv weights Bc Br) time j).plan := by
    rw [field_plan]
    exact field_ordered cache hOrdered j
  have hc : GeneralPaperEpochFieldPlan.CodesValid (fieldAt (selected cache Qv weights Bc Br) time j).plan := by
    rw [field_plan]
    exact field_codes cache hCodes j
  have he := GeneralPaperAdaptiveLossBounds.variations
    (fieldAt (selected cache Qv weights Bc Br) time j) (snapshotAt (selected cache Qv weights Bc Br) time j)
    (choiceAt (selected cache Qv weights Bc Br) time j) (selected_positive cache Qv weights Bc Br time hTime j)
    (snapshot_coherent _ _ _) ho hc
  have ha := field_alphabet (selected cache Qv weights Bc Br) time j
  cases learner with
  | p => simpa only [increment,width,ha] using he.1
  | q => simpa only [increment,width,ha] using he.2.1
  | lambda => simpa only [increment,width,ha] using he.2.2.1
  | mu => simpa only [increment,width,ha] using he.2.2.2

end Blotto.GeneralPaperCatalogueLossBounds
