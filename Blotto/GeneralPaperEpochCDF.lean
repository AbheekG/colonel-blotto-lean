import Blotto.GeneralPaperGeometricVariation

/-! Instantiation of CDF stability at the selected epoch length and the
actual geometric integer-level law. The increment history is arbitrary and
may be chosen from prior rounded queries. No independence of increments is
assumed. The per-step ordered-loss bound is still an explicit obligation of
the query-to-increment refinement.
-/
namespace Blotto.GeneralPaperEpochCDF
open scoped BigOperators Classical
open GeneralPaperOrderedVariation GeneralPaperCDFReweighting
open GeneralPaperGeometricLevels GeneralPaperGeometricVariation
set_option autoImplicit false

theorem epoch_rate (lambda k count : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period) :
    4*((GeneralPaperSourceParameters.prepare k).eta:ℝ)*count≤1/4096 := by
  have he := congrArg (fun q : ℚ => (q:ℝ)) (GeneralPaperSourceParameters.period_eta lambda k)
  push_cast at he
  norm_num at he
  have hc : (count:ℝ)≤(GeneralPaperTrajectoryParameters.prepare lambda k).period := by exact_mod_cast hCount
  have hp : (0:ℝ)≤(GeneralPaperSourceParameters.prepare k).eta :=
    by exact_mod_cast (GeneralPaperSourceParameters.positive k).2.1.le
  have hm := mul_le_mul_of_nonneg_left hc hp
  nlinarith

theorem epoch_power_bounds {n : ℕ} (hn : 0<n) (lambda k count : ℕ)
    (increment : ℕ → Fin n → ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hLoss : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (i : Fin n) :
    31/32≤(geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels increment count i ∧
      (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels increment count i≤1 := by
  have hp := GeneralPaperSourceParameters.positive k
  have he := geometric_bounds hn increment _ _ hp.2.1 hp.2.2.2
    (GeneralPaperSourceParameters.eta_theta k) hLoss count i
  have hr := epoch_rate lambda k count hCount
  exact ⟨by linarith,he.2⟩

theorem epoch_power_variation {n : ℕ} (hn : 0<n) (lambda k count : ℕ)
    (increment : ℕ → Fin n → ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hLoss : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4) :
    variation (fun i => (geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels increment count (code hn i)) (n-1)≤1/4096 := by
  have hp := GeneralPaperSourceParameters.positive k
  exact (geometric_variation hn increment _ _ hp.2.1 hp.2.2.2
    (GeneralPaperSourceParameters.eta_theta k) hLoss count).trans (epoch_rate lambda k count hCount)

theorem epoch_cdf_close {n : ℕ} (hn : 0<n) (lambda k count : ℕ)
    (increment : ℕ → Fin n → ℕ) (p q : ℕ → ℝ) (nu : ℝ)
    (hp : ProbabilityOn p (n-1)) (hq : ProbabilityOn q (n-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose p q (n-1) nu)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (prefixCount : ℕ) (hPrefixCount : prefixCount≤n) :
    |reweightedCDF p (fun i => (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels increment count (code hn i)) (n-1) prefixCount-
      reweightedCDF q (fun i => (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels increment count (code hn i)) (n-1) prefixCount|≤34*nu/31 := by
  apply epoch_reweighted_close p q _ (n-1) nu hp hq hClose
  · intro i _
    exact epoch_power_bounds hn lambda k count increment hCount hMagnitude (code hn i)
  · have he := epoch_power_variation hn lambda k count increment hCount hVariation
    linarith
  · omega

theorem interval_error (a b c d nu : ℝ) (h1 : |a-b|≤nu) (h2 : |c-d|≤nu) :
    |(a-c)-(b-d)|≤2*nu := by
  have he := abs_add_le (a-b) (-(c-d))
  rw [abs_neg] at he
  have hEq : a-b-(c-d)=a-c-(b-d) := by ring
  change |a-b-(c-d)|≤|a-b|+|c-d| at he
  rw [hEq] at he
  linarith

theorem fresh_query_error (exactCDF summaryCDF queryCDF nu : ℝ) (hNu : 0<nu)
    (hSummary : |exactCDF-summaryCDF|≤34*nu/31) (hPower : |summaryCDF-queryCDF|<nu/128) :
    |exactCDF-queryCDF|<5*nu := by
  have he := abs_add_le (exactCDF-summaryCDF) (summaryCDF-queryCDF)
  have hEq : exactCDF-summaryCDF+(summaryCDF-queryCDF)=exactCDF-queryCDF := by ring
  rw [hEq] at he
  linarith

end Blotto.GeneralPaperEpochCDF
