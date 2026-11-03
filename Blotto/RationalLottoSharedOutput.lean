import Blotto.RationalLottoSharedRefinement
import Blotto.RationalLottoFallback

/-! The one-state whole runner uses the same direct budget fallback as the
paper sampler. Exact output equality transfers all existing output laws. -/

namespace Blotto.RationalLottoResourceSystem

def sharedFixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin n → ℚ :=
  (i.runShared K R outerBits scalarBits choiceBits).1.getD i.fallbackAllocation

theorem sharedFixedSample_refines {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.sharedFixedSample K R outerBits scalarBits choiceBits =
      (i.machine K outerBits scalarBits).output R (i.samplingStart K outerBits scalarBits) i.fallbackAllocation choiceBits := by
  rw [sharedFixedSample, i.runShared_refines]
  rfl

end Blotto.RationalLottoResourceSystem
