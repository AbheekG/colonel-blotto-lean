import Blotto.GeneralPaperIntervalQuery

/-! Reference semantics and actual cached implementation of a separately
rounded interval. The common denominator is the complete occurrence total.
-/
namespace Blotto.GeneralPaperRankedInterval
open scoped BigOperators
open GeneralPaperSelectedRank
set_option autoImplicit false
set_option maxHeartbeats 3500000

def referenceNumerator (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (lo hi : ℕ) : ℕ :=
  GeneralPaperPrefixInterval.numerator preparedPrefix (lookup k summary lo).position (lookup k summary hi).position

def referenceCount (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (lo hi : ℕ) : ℕ :=
  (GeneralPaperIntervalQuery.evaluate k preparedPrefix (lookup k summary lo).position (lookup k summary hi).position).quotient

def referenceValue (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (lo hi : ℕ) : ℚ :=
  GeneralPaperRoundedLosses.component (GeneralPaperSourceParameters.prepare k).meshDenominator
    (referenceCount k summary preparedPrefix lo hi)

theorem cached_count {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (cuts : FixedArrayTable m ℕ) (lo hi : Fin m) :
    (GeneralPaperIntervalQuery.cached k preparedPrefix (GeneralPaperRankCache.build k summary cuts).1 lo hi).quotient=
      referenceCount k summary preparedPrefix (cuts.read lo) (cuts.read hi) := by
  unfold GeneralPaperIntervalQuery.cached referenceCount
  rw [GeneralPaperRankCache.read_build,GeneralPaperRankCache.read_build]

theorem numerator_occurrences (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (lo hi : ℕ) (hOrder : lo≤hi) :
    referenceNumerator k summary (GeneralPaperEpochPrefixArray.build values) lo hi=
      ∑ r, if lo≤summary.read r ∧ summary.read r<hi then values.read r else 0 := by
  rw [referenceNumerator,GeneralPaperPrefixInterval.numerator_sum values _ _ (lookup_monotone k summary hMono hOrder)]
  apply Finset.sum_congr rfl
  intro r _
  have hl := lookup_spec k summary hMono lo r
  have hh := lookup_spec k summary hMono hi r
  have he : ((lookup k summary lo).position.val≤r.val ∧ r.val<(lookup k summary hi).position.val) ↔
      (lo≤summary.read r ∧ summary.read r<hi) := by omega
  simp only [he]

theorem count_bound (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (lo hi : ℕ) :
    referenceCount k summary (GeneralPaperEpochPrefixArray.build values) lo hi≤(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  GeneralPaperIntervalQuery.count_bound k values _ _ hTotal

theorem value_bounds (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (lo hi : ℕ) :
    0≤referenceValue k summary (GeneralPaperEpochPrefixArray.build values) lo hi ∧
      referenceValue k summary (GeneralPaperEpochPrefixArray.build values) lo hi≤1 :=
  GeneralPaperIntervalQuery.value_bounds k values _ _ hTotal

theorem lower_count_antitone (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hi : ℕ) :
    Antitone (fun lo => referenceCount k summary (GeneralPaperEpochPrefixArray.build values) lo hi) := by
  intro small large hOrder
  exact GeneralPaperIntervalQuery.lower_count_antitone k values _ hTotal (lookup_monotone k summary hMono hOrder)

theorem lower_value_antitone (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hi : ℕ) :
    Antitone (fun lo => referenceValue k summary (GeneralPaperEpochPrefixArray.build values) lo hi) := by
  intro small large hOrder
  have he := lower_count_antitone k summary values hMono hTotal hi hOrder
  unfold referenceValue GeneralPaperRoundedLosses.component
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast he

theorem empty_count (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (cut : ℕ) :
    referenceCount k summary (GeneralPaperEpochPrefixArray.build values) cut cut=0 :=
  GeneralPaperIntervalQuery.empty_count k values _ hTotal

theorem same_lower_position (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (hMono : Monotone summary.read) (lo other hi : ℕ)
    (hSame : ∀ r, summary.read r<lo ↔ summary.read r<other) :
    referenceCount k summary preparedPrefix lo hi=referenceCount k summary preparedPrefix other hi := by
  unfold referenceCount
  rw [GeneralPaperCellCDFConstancy.same_members_position k summary hMono lo other hSame]

end Blotto.GeneralPaperRankedInterval
