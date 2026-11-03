import Blotto.GeneralPaperWeightedDeviationLaw

/-! Construct the paper's uniform quantiles from the actual weighted law
of y_j/p_j. Their data depend only on the deviation and field weights,
never on a defender row. Mean and both CDF bounds are derived. -/
namespace Blotto.GeneralPaperWeightedLowerQuantile
open GeneralPaperCircleFiniteAverage GeneralPaperCircleThresholdRank
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def original {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (y : Fin g → ℝ) : Fin W → ℝ :=
  GeneralPaperWeightedDeviationLaw.sorted W weights hs (GeneralPaperWeightedDeviationLaw.deviation W weights y)

noncomputable def quantiles {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (y : Fin g → ℝ) : Fin R → ℝ :=
  GeneralPaperLowerQuantile.row R W hR hW (original W weights hs y)

theorem original_monotone {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (y : Fin g → ℝ) :
    Monotone (original W weights hs y) := GeneralPaperWeightedDeviationLaw.sorted_monotone _ _ _ _

theorem original_nonnegative {g : ℕ} (W : ℕ) (weights : Fin g → ℕ) (hs : ∑ j,weights j=W)
    (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (i : Fin W) : 0≤original W weights hs y i :=
  GeneralPaperWeightedDeviationLaw.sorted_nonnegative _ _ _ _
    (GeneralPaperWeightedDeviationLaw.deviation_nonnegative W weights y hy) i

theorem nonnegative {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W)
    (weights : Fin g → ℕ) (hs : ∑ j,weights j=W) (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (a : Fin R) :
    0≤quantiles R W hR hW weights hs y a :=
  GeneralPaperLowerQuantile.nonnegative R W hR hW _ (original_nonnegative W weights hs y hy) a

theorem mean_bound {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hp : ∀ j,0<weights j) (hs : ∑ j,weights j=W) (y : Fin g → ℝ) (hy : ∀ j,0≤y j) :
    average (quantiles R W hR hW weights hs y)≤∑ j,y j := by
  have h := GeneralPaperLowerQuantileMean.mean_bound R W hR hW (original W weights hs y)
    (original_monotone W weights hs y) (original_nonnegative W weights hs y hy)
  exact h.trans_eq (GeneralPaperWeightedDeviationLaw.deviation_mean W hW weights hp hs y)

theorem strict_error {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (t : ℝ) :
    0≤(strict (quantiles R W hR hW weights hs y) t:ℝ)/R-
        (∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j<t then 1 else 0)) ∧
      (strict (quantiles R W hR hW weights hs y) t:ℝ)/R-
        (∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j<t then 1 else 0))≤1/(R:ℝ) := by
  have h := GeneralPaperLowerQuantileCDF.strict_error R W hR hW (original W weights hs y)
    (original_monotone W weights hs y) (original_nonnegative W weights hs y hy) t
  have he : (strict (original W weights hs y) t:ℝ)/W=
      ∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j<t then 1 else 0) := by
    unfold strict
    rw [←average_indicator]
    exact GeneralPaperWeightedDeviationLaw.sorted_average W weights hs (GeneralPaperWeightedDeviationLaw.deviation W weights y) (fun z => if z<t then (1:ℝ) else 0)
  rw [he] at h
  exact h

theorem weak_error {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (t : ℝ) :
    0≤(weak (quantiles R W hR hW weights hs y) t:ℝ)/R-
        (∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j≤t then 1 else 0)) ∧
      (weak (quantiles R W hR hW weights hs y) t:ℝ)/R-
        (∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j≤t then 1 else 0))≤1/(R:ℝ) := by
  have h := GeneralPaperLowerQuantileCDF.weak_error R W hR hW (original W weights hs y)
    (original_monotone W weights hs y) (original_nonnegative W weights hs y hy) t
  have he : (weak (original W weights hs y) t:ℝ)/W=
      ∑ j,((weights j:ℝ)/W)*(if GeneralPaperWeightedDeviationLaw.deviation W weights y j≤t then 1 else 0) := by
    unfold weak
    rw [←average_indicator]
    exact GeneralPaperWeightedDeviationLaw.sorted_average W weights hs (GeneralPaperWeightedDeviationLaw.deviation W weights y) (fun z => if z≤t then (1:ℝ) else 0)
  rw [he] at h
  exact h

theorem attacker_error {g : ℕ} (R W : ℕ) (hR : 0<R) (hW : 0<W) (weights : Fin g → ℕ)
    (hs : ∑ j,weights j=W) (y : Fin g → ℝ) (hy : ∀ j,0≤y j) (t : ℝ) :
    0≤(∑ j,((weights j:ℝ)/W)*share (GeneralPaperWeightedDeviationLaw.deviation W weights y j) t)-
        average (fun a => share (quantiles R W hR hW weights hs y a) t) ∧
      (∑ j,((weights j:ℝ)/W)*share (GeneralPaperWeightedDeviationLaw.deviation W weights y j) t)-
        average (fun a => share (quantiles R W hR hW weights hs y a) t)≤1/(R:ℝ) := by
  have h := GeneralPaperLowerQuantileCDF.attacker_share_error R W hR hW (original W weights hs y)
    (original_monotone W weights hs y) (original_nonnegative W weights hs y hy) t
  unfold original at h
  rw [GeneralPaperWeightedDeviationLaw.sorted_average W weights hs (GeneralPaperWeightedDeviationLaw.deviation W weights y) (fun z => share z t)] at h
  exact h

end Blotto.GeneralPaperWeightedLowerQuantile
