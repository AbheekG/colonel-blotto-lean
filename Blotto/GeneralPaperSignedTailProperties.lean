import Blotto.GeneralPaperSignedTailPlan

/-! Per-sign tails are antitone mesh probabilities with a common total.
Their signed difference has magnitude at most one and ordered variation at
most two. All exact code sums below are analysis only.
-/
namespace Blotto.GeneralPaperSignedTailProperties
open scoped BigOperators
open GeneralPaperRankedInterval GeneralPaperLossVariation
set_option autoImplicit false
set_option maxHeartbeats 3500000

def tailCount (k offset width : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (a : ℕ) : ℕ :=
  referenceCount k summary preparedPrefix (offset+a) (offset+width)

def tailValue (k offset width : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (a : ℕ) : ℚ :=
  referenceValue k summary preparedPrefix (offset+a) (offset+width)

def signedValue (k U : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ) (a : ℕ) : ℚ :=
  tailValue k 0 U summary preparedPrefix a-tailValue k U U summary preparedPrefix a

theorem tail_count_bound (k offset width : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (a : ℕ) :
    tailCount k offset width summary (GeneralPaperEpochPrefixArray.build values) a≤(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  count_bound k summary values hTotal _ _

theorem tail_bounds (k offset width : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (a : ℕ) :
    0≤tailValue k offset width summary (GeneralPaperEpochPrefixArray.build values) a ∧
      tailValue k offset width summary (GeneralPaperEpochPrefixArray.build values) a≤1 := value_bounds k summary values hTotal _ _

theorem tail_count_antitone (k offset width : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    Antitone (tailCount k offset width summary (GeneralPaperEpochPrefixArray.build values)) := by
  intro small large hOrder
  exact lower_count_antitone k summary values hMono hTotal _ (show offset+small≤offset+large by omega)

theorem tail_antitone (k offset width : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    Antitone (tailValue k offset width summary (GeneralPaperEpochPrefixArray.build values)) := by
  intro small large hOrder
  exact lower_value_antitone k summary values hMono hTotal _ (show offset+small≤offset+large by omega)

theorem tail_end (k offset width : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) : tailValue k offset width summary (GeneralPaperEpochPrefixArray.build values) width=0 := by
  unfold tailValue referenceValue
  rw [empty_count k summary values hTotal]
  simp [GeneralPaperRoundedLosses.component]

theorem tail_variation (k offset width last : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    GeneralPaperOrderedVariation.variation
      (fun a => (tailValue k offset width summary (GeneralPaperEpochPrefixArray.build values) a:ℝ)) last≤1 := by
  apply unit_antitone_variation
  · intro i _
    exact_mod_cast tail_antitone k offset width summary values hMono hTotal (Nat.le_succ i)
  · exact_mod_cast (tail_bounds k offset width summary values hTotal 0).2
  · exact_mod_cast (tail_bounds k offset width summary values hTotal last).1

theorem signed_magnitude (k U : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hTotal : 0<∑ r, values.read r) (a : ℕ) :
    |signedValue k U summary (GeneralPaperEpochPrefixArray.build values) a|≤1 := by
  have hp := tail_bounds k 0 U summary values hTotal a
  have hn := tail_bounds k U U summary values hTotal a
  unfold signedValue
  apply abs_le.mpr
  constructor <;> linarith

theorem signed_variation (k U last : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (hTotal : 0<∑ r, values.read r) :
    GeneralPaperOrderedVariation.variation
      (fun a => (signedValue k U summary (GeneralPaperEpochPrefixArray.build values) a:ℝ)) last≤2 := by
  have he := subtract_variation
    (fun a => (tailValue k 0 U summary (GeneralPaperEpochPrefixArray.build values) a:ℝ))
    (fun a => (tailValue k U U summary (GeneralPaperEpochPrefixArray.build values) a:ℝ)) last
  have hp := tail_variation k 0 U last summary values hMono hTotal
  have hn := tail_variation k U U last summary values hMono hTotal
  simpa only [signedValue,Rat.cast_sub] using he.trans (by linarith)

end Blotto.GeneralPaperSignedTailProperties
