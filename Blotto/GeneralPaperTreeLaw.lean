import Blotto.GeneralPaperInitialSummary
import Blotto.GeneralPaperSummaryOccurrences

/-! Full-code probability semantics for the cached tree and the actual
epoch-start array. These proofs expose the initial CDFClose interface used
by the retained reweighting analysis.
-/
namespace Blotto.GeneralPaperTreeLaw
open scoped BigOperators Classical
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperIntervalMass
open GeneralPaperGlobalNodeQuery GeneralPaperTreePrefix GeneralPaperQuantileSearch
open GeneralPaperOrderedVariation GeneralPaperCDFReweighting
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def law (k : ℕ) {height : ℕ} (node : Node height) (i : ℕ) : ℝ :=
  ((GeneralPaperCachedMassJoin.base k:ℚ)^levelAt node i:ℝ)/(globalMass (GeneralPaperCachedMassJoin.base k) node:ℝ)

theorem prefix_law (k : ℕ) {height : ℕ} (node : Node height) (count : ℕ) :
    prefixMass (law k node) count=(cdf k node count:ℝ) := by
  unfold prefixMass law cdf GeneralPaperTreePrefix.weightedPrefix trueMass prefixWeights
  simp only [pow_zero,one_mul]
  push_cast
  rw [Finset.sum_div]

theorem probability_on (k : ℕ) {height : ℕ} (node : Node height) : ProbabilityOn (law k node) (2^height-1) := by
  have hU : 0<2^height := Nat.two_pow_pos _
  constructor
  · intro i _
    have hWeight : (0:ℚ)≤GeneralPaperCachedMassJoin.base k^levelAt node i :=
      pow_nonneg (GeneralPaperCachedMassJoin.base_positive k).le _
    have hTotal := global_mass_positive _ (GeneralPaperCachedMassJoin.base_positive k) node
    unfold law
    exact div_nonneg (by exact_mod_cast hWeight) (by exact_mod_cast hTotal.le)
  · rw [Nat.sub_add_cancel (by omega),prefix_law,cdf_total]
    norm_num

theorem prefix_uniform {s : ℕ} (location : Fin s → ℕ) (count : ℕ) :
    prefixMass (GeneralPaperSummaryOccurrences.uniform location) count=
      (GeneralPaperQuantileOccurrenceCount.summaryCDF location count:ℝ) := by
  rw [GeneralPaperSummaryOccurrences.uniform,GeneralPaperSummaryOccurrences.prefix_identity]
  unfold GeneralPaperSummaryOccurrences.occurrencePrefix
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  unfold GeneralPaperQuantileOccurrenceCount.summaryCDF GeneralPaperQuantileOccurrenceCount.count
  push_cast
  ring

theorem initial_close (lambda k height : ℕ) (node : Node height) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    GeneralPaperCDFReweighting.CDFClose (law k node)
      (GeneralPaperSummaryOccurrences.uniform
        (GeneralPaperInitialSummary.build (GeneralPaperPreparedPowers.prepare lambda k)
          (GeneralPaperQuantileComparison.width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node).read)
      (2^height-1) ((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  intro count hCount
  have hU := Nat.two_pow_pos height
  have hc : count≤2^height := by omega
  have he := GeneralPaperInitialSummary.cdf_error lambda k height node hHeight hValid hPath count hc
  rw [prefix_law,prefix_uniform,abs_sub_comm]
  have hr : |((GeneralPaperQuantileOccurrenceCount.summaryCDF
      (GeneralPaperInitialSummary.build (GeneralPaperPreparedPowers.prepare lambda k)
        (GeneralPaperQuantileComparison.width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node).read count-
      cdf k node count:ℚ):ℝ)|<((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by exact_mod_cast he
  push_cast at hr
  exact hr.le

end Blotto.GeneralPaperTreeLaw
