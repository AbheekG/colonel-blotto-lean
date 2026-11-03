import Blotto.GeneralPaperSummaryOccurrences

/-! The ordered CDF in the reweighting argument is the current exact
geometric learner law. Reweighting its epoch-start law by local levels gives
the global law after all updates. No alternative trajectory or independent
resampling of coordinates is introduced.
-/
namespace Blotto.GeneralPaperEpochLaw
open scoped BigOperators Classical
open SparseMW GeneralPaperGeometricLevels GeneralPaperGeometricVariation
open GeneralPaperOrderedVariation GeneralPaperCDFReweighting
set_option autoImplicit false

theorem sum_codes {n : ℕ} (hn : 0<n) (f : Fin n → ℝ) :
    prefixMass (fun i => f (code hn i)) n=∑ i, f i := by
  unfold prefixMass
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [code_valid]

theorem prefix_divide (f : ℕ → ℝ) (divisor : ℝ) (count : ℕ) :
    prefixMass (fun i => f i/divisor) count=prefixMass f count/divisor := by
  simp only [prefixMass,div_eq_mul_inv,Finset.sum_mul]

theorem probability_ratio {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (t : ℕ) (i : Fin n) :
    probability base increment t i=(weights base increment t i:ℝ)/(∑ j, (weights base increment t j:ℝ)) := by
  simp only [probability,normalizedReal,normalizeQ,Rat.cast_div,Rat.cast_sum]

theorem weights_epoch {n : ℕ} (base : ℚ) (increment : ℕ → Fin n → ℕ) (start count : ℕ) (i : Fin n) :
    weights base increment (start+count) i=
      weights base increment start i*base^levels (fun t => increment (start+t)) count i := by
  unfold weights
  rw [levels_epoch,pow_add]

theorem probability_on_codes {n : ℕ} (hn : 0<n) (base : ℚ) (hBase : 0<base)
    (increment : ℕ → Fin n → ℕ) (t : ℕ) :
    ProbabilityOn (fun i => probability base increment t (code hn i)) (n-1) := by
  constructor
  · intro i _
    exact (probability_positive hn base hBase increment t _).le
  · have he := sum_codes hn (probability base increment t)
    have hSize : n-1+1=n := by omega
    rw [hSize,he]
    exact probability_sum hn base hBase increment t

theorem current_cdf_identity {n : ℕ} (hn : 0<n) (base : ℚ) (hBase : 0<base)
    (increment : ℕ → Fin n → ℕ) (start count prefixCount : ℕ) :
    prefixMass (fun i => probability base increment (start+count) (code hn i)) prefixCount=
      reweightedCDF (fun i => probability base increment start (code hn i))
        (fun i => (base:ℝ)^levels (fun t => increment (start+t)) count (code hn i)) (n-1) prefixCount := by
  let Z := ∑ j, (weights base increment start j:ℝ)
  let newZ := ∑ j, (weights base increment (start+count) j:ℝ)
  have hZ : 0<Z := by
    dsimp only [Z]
    exact_mod_cast weightSum_positive hn _ (weights_positive base hBase increment start)
  have hNewZ : 0<newZ := by
    dsimp only [newZ]
    exact_mod_cast weightSum_positive hn _ (weights_positive base hBase increment (start+count))
  have hPoint : (fun i => (base:ℝ)^levels (fun t => increment (start+t)) count (code hn i)*
      probability base increment start (code hn i))=
      (fun i => (weights base increment (start+count) (code hn i):ℝ)/Z) := by
    funext i
    rw [probability_ratio,weights_epoch]
    push_cast
    dsimp only [Z]
    ring
  have hWeighted : ∀ k, weightedPrefix (fun i => probability base increment start (code hn i))
      (fun i => (base:ℝ)^levels (fun t => increment (start+t)) count (code hn i)) k=
      prefixMass (fun i => (weights base increment (start+count) (code hn i):ℝ)) k/Z := by
    intro k
    unfold weightedPrefix
    rw [hPoint,prefix_divide]
  have hP : (fun i => probability base increment (start+count) (code hn i))=
      (fun i => (weights base increment (start+count) (code hn i):ℝ)/newZ) := by
    funext i
    exact probability_ratio base increment (start+count) (code hn i)
  rw [hP,prefix_divide]
  unfold reweightedCDF
  rw [hWeighted,hWeighted,show n-1+1=n by omega,
    sum_codes hn (fun i => (weights base increment (start+count) i:ℝ))]
  change _/newZ=(_/Z)/(newZ/Z)
  field_simp

theorem selected_epoch_summary {n : ℕ} (hn : 0<n) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (summary : ℕ → ℝ) (nu : ℝ)
    (hSummary : ProbabilityOn summary (n-1))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment start (code hn i)) summary (n-1) nu)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (prefixCount : ℕ) (hPrefixCount : prefixCount≤n) :
    |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) prefixCount-
      reweightedCDF summary (fun i => (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels (fun t => increment (start+t)) count (code hn i))
        (n-1) prefixCount|≤34*nu/31 := by
  have hp := GeneralPaperSourceParameters.positive k
  have hb := base_bounds _ _ hp.2.1 hp.2.2.2 (GeneralPaperSourceParameters.eta_theta k)
  have hBase : 0<geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta :=
    by linarith [hb.1]
  rw [current_cdf_identity hn _ hBase increment start count prefixCount]
  exact GeneralPaperEpochCDF.epoch_cdf_close hn lambda k count (fun t => increment (start+t)) _ summary nu
    (probability_on_codes hn _ hBase increment start) hSummary hClose hCount
    (fun t i => hMagnitude (start+t) i) (fun t => hVariation (start+t)) prefixCount hPrefixCount

theorem selected_occurrence_query {n s : ℕ} (hn : 0<n) (hs : 0<s) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (location : Fin s → Fin n) (nu powerError : ℝ)
    (hNu : 0<nu) (hPowerError : powerError≤nu/1024)
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1) nu)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (roundedPower : Fin s → ℝ) (hRounded : ∀ r, 0≤roundedPower r)
    (hError : ∀ r, |(geometricBase (GeneralPaperSourceParameters.prepare k).eta
      (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels (fun t => increment (start+t)) count (location r)-
      roundedPower r|≤powerError) (prefixCount : ℕ) (hPrefixCount : prefixCount≤n) :
    |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) prefixCount-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location r).val) roundedPower prefixCount/
        (∑ r, roundedPower r)|<5*nu := by
  let value := fun i : ℕ => (geometricBase (GeneralPaperSourceParameters.prepare k).eta
    (GeneralPaperSourceParameters.prepare k).theta:ℝ)^levels (fun t => increment (start+t)) count (code hn i)
  have hLocation : ∀ r, (location r).val≤n-1 := fun r => by have := (location r).isLt; omega
  have hSummary := GeneralPaperSummaryOccurrences.uniform_probability hs (fun r => (location r).val) (n-1) hLocation
  have he := selected_epoch_summary hn lambda k start count increment _ nu hSummary hClose hCount hMagnitude hVariation prefixCount hPrefixCount
  have hRewrite := GeneralPaperSummaryOccurrences.uniform_reweighted_cdf (fun r => (location r).val)
    (n-1) prefixCount value hLocation
  change _≤34*nu/31 at he
  change |_-reweightedCDF _ value (n-1) prefixCount|≤34*nu/31 at he
  rw [hRewrite] at he
  have hLower : ∀ r, (1/2:ℝ)≤value (location r).val := by
    intro r
    dsimp only [value]
    rw [code_valid]
    have h := GeneralPaperEpochCDF.epoch_power_bounds hn lambda k count
      (fun t => increment (start+t)) hCount (fun t i => hMagnitude (start+t) i) (location r)
    linarith [h.1]
  have hErr : ∀ r, |value (location r).val-roundedPower r|≤powerError := by
    intro r
    dsimp only [value]
    rw [code_valid]
    exact hError r
  have hf := GeneralPaperSummaryOccurrences.fresh_power_cdf_error (fun r => (location r).val) (n-1) hLocation
    (fun r => value (location r).val) roundedPower powerError hLower hRounded hErr hs prefixCount
  have hfStrict : |GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location r).val)
      (fun r => value (location r).val) prefixCount/(∑ r, value (location r).val)-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location r).val) roundedPower prefixCount/(∑ r, roundedPower r)|<nu/128 := by
    linarith
  exact GeneralPaperEpochCDF.fresh_query_error _ _ _ nu hNu he hfStrict

end Blotto.GeneralPaperEpochLaw
