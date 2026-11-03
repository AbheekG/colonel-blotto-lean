import Blotto.BinarySegmentCategorical
import Blotto.BinarySegmentPoint
import Blotto.RationalSegmentFlat

/-! Actual Boolean categorical selection and midpoint interpolation compose to
whole canonical allocation words. Exact all-seed refinement transfers the
retained independent flat-bit law and marginal CDF bound. Full time and peak
storage composition is not asserted by this semantic join. -/

namespace Blotto.BinarySegmentSampler
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment

def sample {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (choice : Fin R → Bool) (scalar : Fin K → Bool) : FixedArrayTable n SignedWord :=
  BinarySegmentPoint.sample table (BinarySegmentCategorical.output table source hC hR fallback R choice) K scalar

theorem sample_canonical {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (choice : Fin R → Bool) (scalar : Fin K → Bool) : ∀ j, CanonicalWord ((sample table source hC hR fallback R K choice scalar).read j) :=
  BinarySegmentPoint.sample_canonical table _ K scalar hC

theorem sample_value {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (choice : Fin R → Bool) (scalar : Fin K → Bool) (j : Fin n) :
    value ((sample table source hC hR fallback R K choice scalar).read j) = source.sample fallback R K choice scalar j := by
  unfold sample
  rw [BinarySegmentPoint.sample_value table source hC hR,BinarySegmentCategorical.output_refines]
  rfl

def flatSample {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (bits : Fin (R + K) → Bool) : FixedArrayTable n SignedWord :=
  sample table source hC hR fallback R K (firstBitBlock R K bits) (secondBitBlock R K bits)

theorem flatSample_canonical {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (bits : Fin (R + K) → Bool) : ∀ j, CanonicalWord ((flatSample table source hC hR fallback R K bits).read j) :=
  sample_canonical table source hC hR fallback R K _ _

theorem flatSample_value {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ)
    (bits : Fin (R + K) → Bool) (j : Fin n) :
    value ((flatSample table source hC hR fallback R K bits).read j) = source.flatSample fallback R K bits j :=
  sample_value table source hC hR fallback R K _ _ j

theorem flatSample_fullBudget {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ) (B : ℝ)
    (hBudget : ∀ slot, FullBudget B (source.real.P slot) ∧ FullBudget B (source.real.Q slot))
    (bits : Fin (R + K) → Bool) : FullBudget B (fun j => (value ((flatSample table source hC hR fallback R K bits).read j) : ℝ)) := by
  have hValues : (fun j => (value ((flatSample table source hC hR fallback R K bits).read j) : ℝ)) =
      fun j => (source.flatSample fallback R K bits j : ℝ) := by
    funext j; exact congrArg (fun q : ℚ => (q : ℝ)) (flatSample_value table source hC hR fallback R K bits j)
  rw [hValues]
  exact source.flatSample_fullBudget fallback R K hBudget bits

noncomputable def flatLaw {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ) : Mixed n :=
  (fairBitLaw (R+K)).map (fun bits j => (value ((flatSample table source hC hR fallback R K bits).read j) : ℝ))

theorem flatLaw_eq {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (R K : ℕ) :
    flatLaw table source hC hR fallback R K = source.flatLaw fallback R K := by
  unfold flatLaw RationalSegmentLottery.flatLaw
  congr 1
  funext bits j
  rw [flatSample_value]

theorem flatLaw_CDF_error {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hC : table.Canonical) (hR : table.Refines source) (fallback : Fin k) (K : ℕ) :
    CDFClose (flatLaw table source hC hR fallback (3*(k-1+K)) K) source.real.law (3/(2*(2:ℝ)^K)) := by
  rw [flatLaw_eq]
  exact source.flatLaw_CDF_error fallback K

end Blotto.BinarySegmentSampler
