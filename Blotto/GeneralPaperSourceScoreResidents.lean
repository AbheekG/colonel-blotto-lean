import Blotto.GeneralPaperScoreResidentPhases

/-! Source-derived matrix residency and strict-threshold windows. Both
normalizations use the actual short proxy's height; the original input
budget height is not multiplied into repeated score/DP/scan storage. -/
namespace Blotto.GeneralPaperSourceScoreResidents
open GeneralPaperProxyParameters GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem anchors {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal) :
    ∀ j l,RationalHeight ((columns.read j).anchors.read l) (GeneralPaperSourceScoreHeights.anchorHeight m k) := by
  intro j l
  change RationalHeight ((GeneralPaperRowQuantizer.dictionary columns).anchor j l) _
  rw [hColumns,GeneralPaperSourceUnchangedDictionary.eq_prepared k Qv hQv weights hp hs b reciprocal]
  exact GeneralPaperSourceScoreHeights.prepared_anchors k Qv hQv weights hp hs b hb reciprocal j l

def residentProfile (W m k : ℕ) : ℕ := GeneralPaperScoreResidentPhases.residentProfile W m (prepare m k).K (prepare m k).S
  (GeneralPaperSourceScoreHeights.anchorHeight m k)

theorem resident {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal) :
    GeneralPaperScoreResidentPhases.resident model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S columns values≤
      residentProfile W m k :=
  GeneralPaperScoreResidentPhases.resident_bound model W _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k)
    columns values (GeneralPaperScoreScaleParameters.score_cap m k) (anchors k Qv hQv weights hp hs b hb reciprocal columns hColumns)

theorem budget_height (m k : ℕ) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    RationalHeight (opposingBudget m k b reciprocal/ownBudget m k b reciprocal) (2*binaryWordWidth (prepare m k).qbar) :=
  ((GeneralPaperSourceStrictPreparationBits.opposing_height m k b hb reciprocal).div
    (GeneralPaperSourceScoreHeights.own_height m k b hb reciprocal)).mono (by omega)

def thresholdProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperScoreResidentPhases.thresholdProfile model W m (prepare m k).K (prepare m k).S
    (GeneralPaperSourceScoreHeights.anchorHeight m k) (2*binaryWordWidth (prepare m k).qbar)

theorem threshold {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m)
    (hColumns : GeneralPaperRowQuantizer.dictionary columns=GeneralPaperSourceUnchangedDictionary.run k Qv weights b reciprocal) :
    GeneralPaperScoreResidentPhases.thresholdWindow model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values
      (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)≤thresholdProfile model W m k :=
  GeneralPaperScoreResidentPhases.threshold_bound model W _ _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k)
    columns values (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (GeneralPaperScoreScaleParameters.score_cap m k) (anchors k Qv hQv weights hp hs b hb reciprocal columns hColumns)
    (budget_height m k b hb reciprocal)

end Blotto.GeneralPaperSourceScoreResidents
