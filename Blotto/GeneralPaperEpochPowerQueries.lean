import Blotto.GeneralPaperLocalPowerNumerators

/-! The epoch occurrence queries use the actually prepared shared power
table. Their local power-precision assumption is now discharged. The initial
quantile CDF certificate, the exact local levels and loss variation still
must come from the selected interval-tree/epoch execution.
-/
namespace Blotto.GeneralPaperEpochPowerQueries
open scoped BigOperators Classical
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperGeometricLevels
open GeneralPaperOrderedVariation GeneralPaperGeometricVariation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem period_le_rows (lambda k : ℕ) : (GeneralPaperTrajectoryParameters.prepare lambda k).period≤
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows := by
  obtain ⟨r,hr⟩ := GeneralPaperTrajectoryParameters.epochs_dyadic lambda k
  rw [GeneralPaperTrajectoryParameters.rows_product,hr]
  have hp : 1≤2^r := by have := Nat.two_pow_pos r; omega
  have he := Nat.mul_le_mul_right (GeneralPaperTrajectoryParameters.prepare lambda k).period hp
  simpa only [Nat.one_mul] using he

theorem epoch_level_bound {n : ℕ} (hn : 0<n) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (i : Fin n) : levels (fun t => increment (start+t)) count i≤GeneralPaperPowerPrecision.levelBound lambda k :=
  GeneralPaperPowerPrecision.local_level_bound hn lambda k count (fun t => increment (start+t))
    (hCount.trans (period_le_rows lambda k)) (fun t i => hIncrement (start+t) i) i

theorem epoch_power_range {n : ℕ} (hn : 0<n) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (i : Fin n) :
    (1/2:ℚ)≤value (query (prepare lambda k) (levels (fun t => increment (start+t)) count i)).number ∧
      value (query (prepare lambda k) (levels (fun t => increment (start+t)) count i)).number≤1 := by
  let degree := levels (fun t => increment (start+t)) count i
  have hBound := epoch_level_bound hn lambda k start count increment hCount hIncrement i
  have hError := query_error lambda k degree hBound
  have hFull := GeneralPaperEpochCDF.epoch_power_bounds hn lambda k count
    (fun t => increment (start+t)) hCount (fun t i => hMagnitude (start+t) i) i
  have hNu : ((GeneralPaperSourceParameters.prepare k).nu:ℝ)≤1 := by
    have he := GeneralPaperSourceParameters.eta_upper k
    have hn := GeneralPaperSourceParameters.nu_eta k
    have hq : (GeneralPaperSourceParameters.prepare k).nu≤1 := by rw [hn]; linarith
    exact_mod_cast hq
  have hErr := abs_le.mp hError
  have hReal : (1/2:ℝ)≤(value (query (prepare lambda k) degree).number:ℝ) ∧
      (value (query (prepare lambda k) degree).number:ℝ)≤1 := by
    have hc := query_certificate lambda k degree hBound
    have hUp : (value (query (prepare lambda k) degree).number:ℝ)≤
        (geometricBase (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta:ℝ)^degree := by
      exact_mod_cast hc.2.2.2.2
    constructor <;> linarith
  constructor
  · have hl : ((1/2:ℚ):ℝ)≤(value (query (prepare lambda k) degree).number:ℝ) := by norm_num; exact hReal.1
    exact_mod_cast hl
  · exact_mod_cast hReal.2

def buildNumerators {s : ℕ} (prepared : Prepared) (localLevels : FixedArrayTable s ℕ) : FixedArrayTable s ℕ :=
  FixedArrayTable.ofFn (fun r => GeneralPaperLocalPowerNumerators.numerator prepared.format.unit
    prepared.format.fractionalBits (query prepared (localLevels.read r)).number)

theorem read_numerators {s : ℕ} (prepared : Prepared) (localLevels : FixedArrayTable s ℕ) (r : Fin s) :
    (buildNumerators prepared localLevels).read r=GeneralPaperLocalPowerNumerators.numerator
      prepared.format.unit prepared.format.fractionalBits (query prepared (localLevels.read r)).number :=
  FixedArrayTable.read_ofFn _ _

theorem materialized_cdf_identity {s : ℕ} (prepared : Prepared) (localLevels : FixedArrayTable s ℕ)
    (location : Fin s → ℕ) (prefixCount : ℕ)
    (hPower : prepared.format.unit=2^prepared.format.fractionalBits)
    (hNormal : ∀ r, Normal prepared.format.unit (query prepared (localLevels.read r)).number)
    (hLow : ∀ r, (1/2:ℚ)≤value (query prepared (localLevels.read r)).number)
    (hHigh : ∀ r, value (query prepared (localLevels.read r)).number≤1) :
    GeneralPaperSummaryOccurrences.occurrencePrefix location
      (fun r => (value (query prepared (localLevels.read r)).number:ℝ)) prefixCount/
      (∑ r, (value (query prepared (localLevels.read r)).number:ℝ))=
    ((∑ r, if location r<prefixCount then (buildNumerators prepared localLevels).read r else 0:ℕ):ℝ)/
      ((∑ r, (buildNumerators prepared localLevels).read r:ℕ):ℝ) := by
  simpa only [read_numerators] using GeneralPaperLocalPowerNumerators.normalized_sum location
    (fun r => (query prepared (localLevels.read r)).number) prepared.format.unit prepared.format.fractionalBits
    hPower hNormal hLow hHigh prefixCount

theorem materialized_total_bounds {s : ℕ} (prepared : Prepared) (localLevels : FixedArrayTable s ℕ)
    (hPower : prepared.format.unit=2^prepared.format.fractionalBits)
    (hNormal : ∀ r, Normal prepared.format.unit (query prepared (localLevels.read r)).number)
    (hLow : ∀ r, (1/2:ℚ)≤value (query prepared (localLevels.read r)).number)
    (hHigh : ∀ r, value (query prepared (localLevels.read r)).number≤1) :
    s*prepared.format.unit≤∑ r, (buildNumerators prepared localLevels).read r ∧
      (∑ r, (buildNumerators prepared localLevels).read r)≤s*(2*prepared.format.unit) := by
  have hEach := fun r => GeneralPaperLocalPowerNumerators.numerator_bounds prepared.format.unit
    prepared.format.fractionalBits hPower (query prepared (localLevels.read r)).number (hNormal r) (hLow r) (hHigh r)
  simp only [read_numerators]
  constructor
  · have he := Finset.sum_le_sum (fun r (_ : r∈Finset.univ) => (hEach r).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using he
  · have he := Finset.sum_le_sum (fun r (_ : r∈Finset.univ) => (hEach r).2)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using he

theorem materialized_total_positive {s : ℕ} (hs : 0<s) (prepared : Prepared) (localLevels : FixedArrayTable s ℕ)
    (hPower : prepared.format.unit=2^prepared.format.fractionalBits)
    (hNormal : ∀ r, Normal prepared.format.unit (query prepared (localLevels.read r)).number)
    (hLow : ∀ r, (1/2:ℚ)≤value (query prepared (localLevels.read r)).number)
    (hHigh : ∀ r, value (query prepared (localLevels.read r)).number≤1) :
    0<∑ r, (buildNumerators prepared localLevels).read r := by
  have he := (materialized_total_bounds prepared localLevels hPower hNormal hLow hHigh).1
  have hu : 0<prepared.format.unit := by rw [hPower]; positivity
  exact (Nat.mul_pos hs hu).trans_le he

theorem cdf_error {n s : ℕ} (hn : 0<n) (hs : 0<s) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (location : Fin s → Fin n)
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (prefixCount : ℕ) (hPrefixCount : prefixCount≤n) :
    |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) prefixCount-
      GeneralPaperSummaryOccurrences.occurrencePrefix (fun r => (location r).val)
        (fun r => (value (query (prepare lambda k) (levels (fun t => increment (start+t)) count (location r))).number:ℝ)) prefixCount/
        (∑ r, (value (query (prepare lambda k) (levels (fun t => increment (start+t)) count (location r))).number:ℝ))|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hNu : (0:ℝ)<(GeneralPaperSourceParameters.prepare k).nu := by
    exact_mod_cast (GeneralPaperSourceParameters.positive k).2.2.1
  apply GeneralPaperEpochLaw.selected_occurrence_query hn hs lambda k start count increment location _ _ hNu
    (le_refl _) hClose hCount hMagnitude hVariation
  · intro r
    exact (query_positive lambda k _ (epoch_level_bound hn lambda k start count increment hCount hIncrement (location r))).le
  · intro r
    exact query_error lambda k _ (epoch_level_bound hn lambda k start count increment hCount hIncrement (location r))
  · exact hPrefixCount

theorem integer_cdf_error {n s : ℕ} (hn : 0<n) (hs : 0<s) (lambda k start count : ℕ)
    (increment : ℕ → Fin n → ℕ) (location : Fin s → Fin n)
    (localLevels : FixedArrayTable s ℕ)
    (hLevels : ∀ r, localLevels.read r=levels (fun t => increment (start+t)) count (location r))
    (hClose : GeneralPaperCDFReweighting.CDFClose
      (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment start (code hn i))
      (GeneralPaperSummaryOccurrences.uniform (fun r => (location r).val)) (n-1)
      ((GeneralPaperSourceParameters.prepare k).nu:ℝ))
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hIncrement : ∀ t i, increment t i≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hMagnitude : ∀ t i, |(executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t i):ℝ)|≤2)
    (hVariation : ∀ t, variation (fun i =>
      (executedLoss (GeneralPaperSourceParameters.prepare k).theta (increment t (code hn i)):ℝ)) (n-1)≤4)
    (prefixCount : ℕ) (hPrefixCount : prefixCount≤n) :
    |prefixMass (fun i => probability (geometricBase (GeneralPaperSourceParameters.prepare k).eta
        (GeneralPaperSourceParameters.prepare k).theta) increment (start+count) (code hn i)) prefixCount-
      ((∑ r, if (location r).val<prefixCount then (buildNumerators (prepare lambda k) localLevels).read r else 0:ℕ):ℝ)/
        ((∑ r, (buildNumerators (prepare lambda k) localLevels).read r:ℕ):ℝ)|<
      5*((GeneralPaperSourceParameters.prepare k).nu:ℝ) := by
  have hBound : ∀ r, localLevels.read r≤GeneralPaperPowerPrecision.levelBound lambda k := by
    intro r
    rw [hLevels]
    exact epoch_level_bound hn lambda k start count increment hCount hIncrement (location r)
  have hNormal : ∀ r, Normal (prepare lambda k).format.unit (query (prepare lambda k) (localLevels.read r)).number :=
    fun r => (query_certificate lambda k _ (hBound r)).2.1
  have hRange : ∀ r, (1/2:ℚ)≤value (query (prepare lambda k) (localLevels.read r)).number ∧
      value (query (prepare lambda k) (localLevels.read r)).number≤1 := by
    intro r
    rw [hLevels]
    exact epoch_power_range hn lambda k start count increment hCount hIncrement hMagnitude (location r)
  have hIdentity := materialized_cdf_identity (prepare lambda k) localLevels (fun r => (location r).val) prefixCount
    (GeneralPaperPowerPrecision.unit_power lambda k) hNormal (fun r => (hRange r).1) (fun r => (hRange r).2)
  rw [← hIdentity]
  simp only [hLevels]
  exact cdf_error hn hs lambda k start count increment location hClose hCount hIncrement hMagnitude hVariation prefixCount hPrefixCount

end Blotto.GeneralPaperEpochPowerQueries
