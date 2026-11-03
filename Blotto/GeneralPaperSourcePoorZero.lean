import Blotto.GeneralPaperScoreMaximum

/-! The actual source's normalized dictionary has all tuples strictly
affordable when its selected poor endpoint is zero. Its actual strict DP
threshold therefore equals the maximum tuple score; no reciprocal is used.
-/
namespace Blotto.GeneralPaperSourcePoorZero
open GeneralPaperProxyParameters GeneralPaperSourceInitializer GeneralPaperInitializerPreparedPoint
open GeneralPaperDictionary GeneralPaperStrictScore
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem prepared_unit {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    GeneralPaperTransferPreparation.UnitDictionary (prepared k Qv hQv weights hp hs b reciprocal).dictionary
      (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
      (GeneralPaperScoreScaleParameters.labels_positive m k) :=
  GeneralPaperTransferPreparation.prepared_unit (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k)
    (sourceRows k Qv weights b reciprocal) (ownBudget m k b reciprocal) (opposingBudget m k b reciprocal)
    (own_positive m k b hb reciprocal) (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
    (source_rows_feasible k Qv hm hQv weights hs b hb reciprocal)

theorem all_slack {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hZero : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0)
    (labels : Fin m → Fin (prepare m k).K) :
    rationalCost (prepared k Qv hQv weights hp hs b true).dictionary labels<
      opposingBudget m k b true/ownBudget m k b true := by
  have hu := prepared_unit k Qv hm hQv weights hp hs b hb true
  have hCost : rationalCost (prepared k Qv hQv weights hp hs b true).dictionary labels≤(m:ℚ) := by
    unfold rationalCost
    calc
      _ ≤ ∑ _j : Fin m,(1:ℚ) := Finset.sum_le_sum (fun j _ => hu.bounded j (labels j))
      _ = _ := by simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,mul_one]
  have hLarge := GeneralPaperPoorZeroGeometry.opposing_gt_fields m k b hb hModify hZero
  exact hCost.trans_lt hLarge

theorem threshold_maximum {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hZero : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint=0) :
    (prepared k Qv hQv weights hp hs b true).threshold=
      GeneralPaperScoreMaximum.maximum (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S := by
  have hRef := GeneralPaperTransferPreparation.reference_threshold
    (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) (GeneralPaperScoreScaleParameters.labels_positive m k)
    (GeneralPaperTrajectoryParameters.labels_divide_rows m (alphabet m k).lambda k) (sourceRows k Qv weights b true)
    (ownBudget m k b true) (opposingBudget m k b true) (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S
  exact hRef.symm.trans (GeneralPaperScoreMaximum.all_slack_threshold _ _ _ (GeneralPaperScoreScaleParameters.labels_positive m k)
    _ (all_slack k Qv hm hQv weights hp hs b hb hModify hZero))

theorem endpoint_positive_of_nonmaximal {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1)
    (hModify : (GeneralPaperProxyClassifier.classify m k b).choice.modify=some .poor)
    (hNonmaximal : (prepared k Qv hQv weights hp hs b true).threshold≠
      GeneralPaperScoreMaximum.maximum (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S) :
    (0:ℝ)<(GeneralPaperProxyClassifier.classify m k b).choice.endpoint := by
  have hn : (GeneralPaperProxyClassifier.classify m k b).choice.modify≠none := by
    intro he
    rw [hModify] at he
    cases he
  have hNonnegative := (GeneralPaperProxyEndpointBounds.endpoint_unit m k b hb hn).1
  have hNe : (GeneralPaperProxyClassifier.classify m k b).choice.endpoint≠0 :=
    fun hz => hNonmaximal (threshold_maximum k Qv hm hQv weights hp hs b hb hModify hz)
  exact_mod_cast lt_of_le_of_ne hNonnegative (Ne.symm hNe)

end Blotto.GeneralPaperSourcePoorZero
