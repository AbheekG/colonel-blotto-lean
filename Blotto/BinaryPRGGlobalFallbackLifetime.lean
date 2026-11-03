import Blotto.BinaryPRGFallbackInventory
import Blotto.BinaryNestedResidualLifetime

/-! The PRG's original B-zero global fallback is an actual traced array copy.
Budget/zero word payloads stay borrowed; the output references and all array
prefixes are reserved. This does not select a local lower-resource fallback. -/
namespace Blotto.BinaryPRGGlobalFallbackLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

def prepareWithTrace {n : ℕ} (input : BinaryLottoResourceInput.Input n) : FixedArrayTable n SignedWord × Trace :=
  BinaryNestedResidualLifetime.copyWithTrace n (fun j => if j.val = 0 then input.budget else BinaryRationalOpcode.zero)

theorem prepareWithTrace_erasure {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    (prepareWithTrace input).1 = BinaryLottoSampler.fallback input := by
  rw [prepareWithTrace,BinaryNestedResidualLifetime.copyWithTrace_erasure]
  rfl

def envelope (n : ℕ) : ℕ := BinaryNestedResidualLifetime.copyEnvelope n

theorem prepareWithTrace_usage {n : ℕ} (input : BinaryLottoResourceInput.Input n) :
    usage (prepareWithTrace input).2 ≤ envelope n :=
  BinaryNestedResidualLifetime.copyWithTrace_usage n _

theorem all_prefix {n : ℕ} (input : BinaryLottoResourceInput.Input n) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareWithTrace input).2 steps ≤ borrowed+envelope n ∧
      framePeak ((prepareWithTrace input).2.take steps) ≤ envelope n :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepareWithTrace_usage input) borrowed steps

end Blotto.BinaryPRGGlobalFallbackLifetime
