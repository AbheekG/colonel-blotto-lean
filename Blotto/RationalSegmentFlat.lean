import Blotto.RationalSegmentLaw
import Blotto.FairBitBlocks

/-! A single finite fair vector supplies both segment-sampling blocks. Its
law equals the verified independent two-block law, and its total length is
explicit. Every output remains a native rational allocation. -/

namespace Blotto.RationalSegmentLottery
open MeasureTheory

def flatSample {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    (bits : Fin (R + K) → Bool) : Fin n → ℚ :=
  l.sample fallback R K (firstBitBlock R K bits) (secondBitBlock R K bits)

noncomputable def flatLaw {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ) : Mixed n :=
  (fairBitLaw (R + K)).map (fun bits j => (l.flatSample fallback R K bits j : ℝ))

theorem flatLaw_eq {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ) :
    l.flatLaw fallback R K = l.cappedLaw fallback R K := by
  calc
    l.flatLaw fallback R K = averagedLaw (fairBitLaw K)
      (fun scalarBits => (fairBitLaw R).map (fun choiceBits j => (l.sample fallback R K choiceBits scalarBits j : ℝ)))
      (measurable_of_countable _) := by
        simpa only [flatLaw, flatSample] using fairBitBlocks_law (n := n) R K
          (fun choiceBits scalarBits => (fun j => (l.sample fallback R K choiceBits scalarBits j : ℝ)))
    _ = l.cappedLaw fallback R K := by
      unfold cappedLaw
      congr 1
      funext scalarBits
      exact (l.fixedLaw_eq_sample fallback R K scalarBits).symm

theorem flatSample_fullBudget {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (R K : ℕ)
    {B : ℝ} (h : ∀ slot, FullBudget B (l.real.P slot) ∧ FullBudget B (l.real.Q slot))
    (bits : Fin (R + K) → Bool) :
    FullBudget B (fun j => (l.flatSample fallback R K bits j : ℝ)) :=
  l.sample_fullBudget fallback R K h _ _

theorem flatLaw_CDF_error {n k : ℕ} (l : RationalSegmentLottery n k) (fallback : Fin k) (K : ℕ) :
    CDFClose (l.flatLaw fallback (3 * (k - 1 + K)) K) l.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  rw [l.flatLaw_eq]
  exact l.cappedLaw_CDF_error fallback K

end Blotto.RationalSegmentLottery
