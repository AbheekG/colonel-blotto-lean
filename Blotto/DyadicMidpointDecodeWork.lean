import Blotto.DyadicMidpointAssemblyCost
import Blotto.BinaryPayloadMergeBitWork

/-! The primary midpoint uses the balanced single-array decoder and one
natural shift for its denominator. This ledger combines available data copies
and primitive prices. Counter/address/container/backend/ownership work remains
separate, and the natural primitive's linear envelope is an explicit hypothesis. -/

namespace Blotto

def dyadicMidpointDecodeBitWork (model : RationalCostModel) (primitive : ℕ → ℕ)
    (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  2 * K + BinaryPayload.balancedBitWork primitive (Array.ofFn bits) 0 K + primitive (K + 2) +
    DyadicMidpointAssembly.materializedBitCost model K bits

theorem dyadicMidpointDecodeBitWork_bound (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (bits : Fin K → Bool) :
    dyadicMidpointDecodeBitWork model primitive K bits ≤
      3 * K + (4 + 2 * c) * K * binaryWordWidth K + c * (K + 2) +
        11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) := by
  have hd := BinaryPayload.balancedBitWork_word_bound primitive c hPrimitive (Array.ofFn bits) 0 K
  have hs := hPrimitive (K + 2)
  have ha := DyadicMidpointAssembly.materializedBitCost_bound model K bits
  unfold dyadicMidpointDecodeBitWork
  omega

theorem balancedBitIndex_reads (K : ℕ) : BinaryPayload.readCount K = K := BinaryPayload.readCount_eq K

theorem balancedBitIndex_merges (K : ℕ) : BinaryPayload.mergeCount K = K - 1 := BinaryPayload.mergeCount_eq K

end Blotto
