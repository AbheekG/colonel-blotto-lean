import Blotto.GeneralPaperCellCDFConstancy

/-! The actual rounded-prefix CDF supplies the unit, endpoint and monotone
hypotheses of the retained loss-variation analysis. Its signed concatenation
has variation at most four, including the zero and sign-boundary cases.
The function here is reference semantics for the precomputed cached queries.
-/
namespace Blotto.GeneralPaperPreparedCDFProperties
open scoped BigOperators
open GeneralPaperRankedCDFQuery GeneralPaperLossVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

def cdf (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (i : ℕ) : ℝ :=
  (referenceValue k summary preparedPrefix (i+1):ℝ)

theorem cdf_bounds (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (i : ℕ) :
    0≤cdf k summary (GeneralPaperEpochPrefixArray.build values) i ∧
      cdf k summary (GeneralPaperEpochPrefixArray.build values) i≤1 := by
  have he := reference_bounds k summary values hTotal (i+1)
  unfold cdf
  constructor
  · exact_mod_cast he.1
  · exact_mod_cast he.2

theorem cdf_monotone (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    Monotone (cdf k summary (GeneralPaperEpochPrefixArray.build values)) := by
  intro i j hij
  have he := reference_monotone k summary values hMono hTotal (show i+1≤j+1 by omega)
  unfold cdf
  exact_mod_cast he

theorem cdf_end (k U : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hU : 0<U) (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hCodes : ∀ r, summary.read r<U) :
    cdf k summary (GeneralPaperEpochPrefixArray.build values) (U-1)=1 := by
  unfold cdf
  rw [Nat.sub_add_cancel (by omega),reference_full k summary values hMono hTotal U hCodes]
  norm_num

theorem cdf_variation (k U : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hU : 0<U) (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) (hCodes : ∀ r, summary.read r<U) :
    GeneralPaperOrderedVariation.variation (cdf k summary (GeneralPaperEpochPrefixArray.build values)) (U-1)≤1 := by
  apply unit_monotone_variation
  · intro i _
    exact cdf_monotone k summary values hMono hTotal (Nat.le_succ i)
  · exact (cdf_bounds k summary values hTotal 0).1
  · exact (cdf_end k U summary values hU hMono hTotal hCodes).le

theorem signed_variation (k U bid : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hU : 0<U) (hBid : bid<U) (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r)
    (hCodes : ∀ r, summary.read r<U) :
    GeneralPaperOrderedVariation.variation
      (signedConcatenation (rowDifference (cdf k summary (GeneralPaperEpochPrefixArray.build values)) bid) (U-1)) (2*U-1)≤4 := by
  have he := signed_loss_variation (cdf k summary (GeneralPaperEpochPrefixArray.build values)) bid (U-1) (by omega)
    (fun i _ => cdf_monotone k summary values hMono hTotal (Nat.le_succ i))
    (cdf_bounds k summary values hTotal 0).1 (cdf_bounds k summary values hTotal 0).2
    (cdf_end k U summary values hU hMono hTotal hCodes)
  have hEnd : 2*(U-1)+1=2*U-1 := by omega
  rw [hEnd] at he
  exact he

theorem source_signed_variation (lambda k height bid : ℕ) (node : GeneralPaperIntervalCache.Node height)
    (hHeight : height≤lambda+1) (hValid : GeneralPaperIntervalCache.Valid lambda k node)
    (hPath : GeneralPaperGlobalNodeQuery.PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (hBid : bid<2^height) :
    let summary := GeneralPaperInitialSummary.build (GeneralPaperPreparedPowers.prepare lambda k)
      (GeneralPaperQuantileComparison.width lambda k) (GeneralPaperSourceParameters.prepare k).summarySize height node
    GeneralPaperOrderedVariation.variation
      (signedConcatenation (rowDifference (cdf k summary (GeneralPaperEpochPrefixArray.build values)) bid) (2^height-1))
        (2*2^height-1)≤4 :=
  signed_variation k (2^height) bid _ values (Nat.two_pow_pos height) hBid
    (GeneralPaperSummaryOrdered.summary_ordered lambda k height node hHeight hValid hPath) hTotal
    (GeneralPaperInitialSummary.code_bounds _ _ _ _ _)

end Blotto.GeneralPaperPreparedCDFProperties
