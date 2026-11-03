import Blotto.GeneralPaperTreeLaw
import Blotto.GeneralPaperEpochPowerQueries

/-! The actual initial summary supplies the retained epoch CDF certificate
whenever the tree's exact code levels are the current learner levels. The
global path cap is derived from the executed increment bound and horizon.
Full construction of that update history remains a separate execution join.
-/
namespace Blotto.GeneralPaperTreeEpochJoin
open scoped BigOperators Classical
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalMass
open GeneralPaperGlobalNodeQuery GeneralPaperCachedMassJoin GeneralPaperGeometricLevels
open GeneralPaperGeometricVariation GeneralPaperOrderedVariation GeneralPaperCDFReweighting
set_option autoImplicit false
set_option maxHeartbeats 3000000

def location (lambda k height : ℕ) (node : Node height) :
    Fin (GeneralPaperSourceParameters.prepare k).summarySize → Fin (2^height) := fun r =>
  ⟨(GeneralPaperInitialSummary.build (GeneralPaperPreparedPowers.prepare lambda k)
    (GeneralPaperQuantileComparison.width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node).read r,
    GeneralPaperInitialSummary.code_bounds _ _ _ _ _ r⟩

theorem history_mass (k height start : ℕ) (node : Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHistory : ∀ i, levelAt node i.val=levels increment start i) :
    globalMass (base k) node=∑ i, weights (base k) increment start i := by
  rw [← global_mass_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hHistory]
  rfl

theorem history_law (k height start : ℕ) (node : Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHistory : ∀ i, levelAt node i.val=levels increment start i) (i : Fin (2^height)) :
    GeneralPaperTreeLaw.law k node i.val=probability (base k) increment start i := by
  rw [GeneralPaperTreeLaw.law,hHistory,history_mass k height start node increment hHistory,
    GeneralPaperEpochLaw.probability_ratio]
  simp only [weights,Rat.cast_sum,Rat.cast_pow]

theorem history_path (lambda k height start : ℕ) (node : Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHistory : ∀ i, levelAt node i.val=levels increment start i)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node := by
  intro i hi
  simp only [Nat.zero_add]
  rw [hHistory ⟨i,hi⟩]
  exact GeneralPaperPowerPrecision.local_level_bound (Nat.two_pow_pos height) lambda k start increment hStart hIncrement _

theorem initial_history_close (lambda k height start : ℕ) (node : Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hHistory : ∀ i, levelAt node i.val=levels increment start i)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    GeneralPaperCDFReweighting.CDFClose (fun i => probability (base k) increment start (code (Nat.two_pow_pos height) i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location lambda k height node r).val))
      (2^height-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hPath := history_path lambda k height start node increment hHistory hStart hIncrement
  have he := GeneralPaperTreeLaw.initial_close lambda k height node hHeight hValid hPath
  intro count hCount
  have hPrefix : prefixMass (fun i => probability (base k) increment start (code (Nat.two_pow_pos height) i)) count=
      prefixMass (GeneralPaperTreeLaw.law k node) count := by
    unfold prefixMass
    apply Finset.sum_congr rfl
    intro i hi
    have hI : i<2^height := by
      have hu := Nat.two_pow_pos height
      have hc := Finset.mem_range.mp hi
      omega
    have hv : (code (Nat.two_pow_pos height) i).val=i := by
      simp only [code,Fin.val_mk,min_eq_left (by omega : i≤2^height-1)]
    simpa only [hv] using (history_law k height start node increment hHistory (code (Nat.two_pow_pos height) i)).symm
  rw [hPrefix]
  exact he count hCount

theorem epoch_cdf_error (lambda k height start count : ℕ) (node : Node height)
    (increment : ℕ → Fin (2^height) → ℕ)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hHistory : ∀ i, levelAt node i.val=levels increment start i)
    (hStart : start≤(GeneralPaperTrajectoryParameters.prepare lambda k).rows)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code (Nat.two_pow_pos height) i)):ℝ)) (2^height-1)≤4)
    (prefixCount : ℕ) (hPrefix : prefixCount≤2^height) :
    |prefixMass (fun i => probability (base k) increment (start+count) (code (Nat.two_pow_pos height) i)) prefixCount-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location lambda k height node r).val)
        (fun r => (GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k)
          (levels (fun t => increment (start+t)) count (location lambda k height node r))).number:ℝ)) prefixCount/
        (∑ r, (GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k)
          (levels (fun t => increment (start+t)) count (location lambda k height node r))).number:ℝ))|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  exact GeneralPaperEpochPowerQueries.cdf_error (Nat.two_pow_pos height) hs lambda k start count increment
    (location lambda k height node) (initial_history_close lambda k height start node increment hHeight hValid hHistory hStart hIncrement)
    hCount hIncrement hMagnitude hVariation prefixCount hPrefix

end Blotto.GeneralPaperTreeEpochJoin
