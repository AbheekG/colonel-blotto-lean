import Blotto.GeneralPaperQueryLossCounts

/-! Exact full-code semantics for the cached primal/response integer
updates. The reference functions are analysis only. Their magnitude and
variation follow from the constructed CDF and per-sign interval queries.
-/
namespace Blotto.GeneralPaperNativeLossReference
open scoped BigOperators
open GeneralPaperQueryLossCounts
set_option autoImplicit false
set_option maxHeartbeats 3500000

def reference (k U : ℕ) (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (a : ℕ) : Counts :=
  ⟨GeneralPaperRankedCDFQuery.referenceCount k cdfSummary cdfPrefix a,
    GeneralPaperRankedCDFQuery.referenceCount k cdfSummary cdfPrefix (a+1),
    GeneralPaperRankedInterval.referenceCount k tailSummary tailPrefix a U,
    GeneralPaperRankedInterval.referenceCount k tailSummary tailPrefix (U+a) (2*U),0⟩

theorem evaluate_loss {m : ℕ} (k U : ℕ) (response : Bool)
    (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    loss k response (evaluate k cdfPrefix tailPrefix (prepare k U cdfSummary tailSummary queries) q)=
      loss k response (reference k U cdfSummary tailSummary cdfPrefix tailPrefix (queries.read q)) := by
  unfold loss evaluate prepare reference
  dsimp only
  rw [GeneralPaperCDFPairPlan.evaluate_lower,GeneralPaperCDFPairPlan.evaluate_upper,
    GeneralPaperSignedTailPlan.evaluate_positive,GeneralPaperSignedTailPlan.evaluate_negative]

theorem evaluate_increment {m : ℕ} (k U : ℕ) (response : Bool)
    (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (queries : FixedArrayTable m ℕ) (q : Fin m) :
    increment k response (evaluate k cdfPrefix tailPrefix (prepare k U cdfSummary tailSummary queries) q)=
      increment k response (reference k U cdfSummary tailSummary cdfPrefix tailPrefix (queries.read q)) := by
  unfold increment evaluate prepare reference
  dsimp only
  rw [GeneralPaperCDFPairPlan.evaluate_lower,GeneralPaperCDFPairPlan.evaluate_upper,
    GeneralPaperSignedTailPlan.evaluate_positive,GeneralPaperSignedTailPlan.evaluate_negative]

theorem reference_bounds (k U : ℕ)
    (cdfSummary tailSummary cdfValues tailValues : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hCDF : 0<∑ r, cdfValues.read r) (hTail : 0<∑ r, tailValues.read r) (a : ℕ) :
    Bounds k (reference k U cdfSummary tailSummary (GeneralPaperEpochPrefixArray.build cdfValues)
      (GeneralPaperEpochPrefixArray.build tailValues) a) := by
  exact ⟨GeneralPaperRankedCDFQuery.reference_count_bound k cdfSummary cdfValues hCDF a,
    GeneralPaperRankedCDFQuery.reference_count_bound k cdfSummary cdfValues hCDF (a+1),
    GeneralPaperRankedInterval.count_bound k tailSummary tailValues hTail _ _,
    GeneralPaperRankedInterval.count_bound k tailSummary tailValues hTail _ _⟩

theorem cdf_variation (k shift last : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    GeneralPaperOrderedVariation.variation
      (fun a => (GeneralPaperRankedCDFQuery.referenceValue k summary (GeneralPaperEpochPrefixArray.build values) (a+shift):ℝ)) last≤1 := by
  apply GeneralPaperLossVariation.unit_monotone_variation
  · intro i _
    exact_mod_cast GeneralPaperRankedCDFQuery.reference_monotone k summary values hMono hTotal (show i+shift≤ i+1+shift by omega)
  · exact_mod_cast (GeneralPaperRankedCDFQuery.reference_bounds k summary values hTotal (0+shift)).1
  · exact_mod_cast (GeneralPaperRankedCDFQuery.reference_bounds k summary values hTotal (last+shift)).2

theorem loss_real_formula (k U : ℕ) (response : Bool)
    (cdfSummary tailSummary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cdfPrefix tailPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (a : ℕ) :
    (loss k response (reference k U cdfSummary tailSummary cdfPrefix tailPrefix a):ℝ)=
      (if response then 0 else 1)-
        ((GeneralPaperRankedCDFQuery.referenceValue k cdfSummary cdfPrefix a:ℝ)+
          (GeneralPaperRankedCDFQuery.referenceValue k cdfSummary cdfPrefix (a+1):ℝ))/2+
        ((GeneralPaperSignedTailProperties.tailValue k 0 U tailSummary tailPrefix a:ℝ)-
          (GeneralPaperSignedTailProperties.tailValue k U U tailSummary tailPrefix a:ℝ)) := by
  unfold loss reference GeneralPaperRankedCDFQuery.referenceValue GeneralPaperSignedTailProperties.tailValue
    GeneralPaperRankedInterval.referenceValue
  cases response <;> simp only [Bool.false_eq_true,ite_false,ite_true,GeneralPaperRoundedLosses.primalLoss,
    GeneralPaperRoundedLosses.responseLoss,Nat.zero_add,two_mul]
    <;> push_cast <;> ring

theorem loss_variation (k U last : ℕ) (response : Bool)
    (cdfSummary tailSummary cdfValues tailValues : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hCDFMono : Monotone cdfSummary.read) (hTailMono : Monotone tailSummary.read)
    (hCDF : 0<∑ r, cdfValues.read r) (hTail : 0<∑ r, tailValues.read r) :
    GeneralPaperOrderedVariation.variation
      (fun a => (loss k response (reference k U cdfSummary tailSummary (GeneralPaperEpochPrefixArray.build cdfValues)
        (GeneralPaperEpochPrefixArray.build tailValues) a):ℝ)) last≤4 := by
  have hl := cdf_variation k 0 last cdfSummary cdfValues hCDFMono hCDF
  have hh := cdf_variation k 1 last cdfSummary cdfValues hCDFMono hCDF
  have hp := GeneralPaperSignedTailProperties.tail_variation k 0 U last tailSummary tailValues hTailMono hTail
  have hn := GeneralPaperSignedTailProperties.tail_variation k U U last tailSummary tailValues hTailMono hTail
  simp only [Nat.add_zero] at hl
  have he := GeneralPaperLossVariation.half_cdf_tail_variation _ _ _ _ last (if response then 0 else 1) hl hh hp hn
  have hf : (fun a => (loss k response (reference k U cdfSummary tailSummary (GeneralPaperEpochPrefixArray.build cdfValues)
        (GeneralPaperEpochPrefixArray.build tailValues) a):ℝ))=
      (fun a => (if response then 0 else 1)-
        ((GeneralPaperRankedCDFQuery.referenceValue k cdfSummary (GeneralPaperEpochPrefixArray.build cdfValues) a:ℝ)+
          (GeneralPaperRankedCDFQuery.referenceValue k cdfSummary (GeneralPaperEpochPrefixArray.build cdfValues) (a+1):ℝ))/2+
        ((GeneralPaperSignedTailProperties.tailValue k 0 U tailSummary (GeneralPaperEpochPrefixArray.build tailValues) a:ℝ)-
          (GeneralPaperSignedTailProperties.tailValue k U U tailSummary (GeneralPaperEpochPrefixArray.build tailValues) a:ℝ))) :=
    funext (loss_real_formula k U response cdfSummary tailSummary _ _)
  rw [hf]
  exact he

theorem executed_variation (k U last : ℕ) (response : Bool)
    (cdfSummary tailSummary cdfValues tailValues : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hCDFMono : Monotone cdfSummary.read) (hTailMono : Monotone tailSummary.read)
    (hCDF : 0<∑ r, cdfValues.read r) (hTail : 0<∑ r, tailValues.read r) :
    GeneralPaperOrderedVariation.variation
      (fun a => (GeneralPaperGeometricLevels.executedLoss (GeneralPaperSourceParameters.prepare k).theta
        (increment k response (reference k U cdfSummary tailSummary (GeneralPaperEpochPrefixArray.build cdfValues)
          (GeneralPaperEpochPrefixArray.build tailValues) a)):ℝ)) last≤4 := by
  have he := loss_variation k U last response cdfSummary tailSummary cdfValues tailValues hCDFMono hTailMono hCDF hTail
  convert he using 1
  congr 1
  funext a
  rw [GeneralPaperQueryLossCounts.increment_loss k response _ (reference_bounds k U cdfSummary tailSummary cdfValues tailValues hCDF hTail a)]

end Blotto.GeneralPaperNativeLossReference
