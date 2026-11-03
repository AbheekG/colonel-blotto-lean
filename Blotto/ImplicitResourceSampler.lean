import Blotto.ImplicitLeafPrefixSamplerLaw
import Blotto.ImplicitResourcePrefix

/-! Actual bounded fair-bit leaf draws respect a rational resource budget on
every path and approximate the exact conditional weighted labelled law for all
bounded tests. A feasible first code is explicit; empty prefixes are not silently
replaced by infeasible allocations. Specific Farey and binary costs remain open. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

theorem resourceCap_nonnegative (C : ℕ) (decode : ℕ → ℚ)
    (hm : MonotoneResourceCuts.MonotoneDecode C decode) (budget : ℚ) (hFirst : decode 0 ≤ budget) :
    0 ≤ MonotoneResourceCuts.cap C decode budget := by
  have he := (MonotoneResourceCuts.cap_contract C decode hm budget 0 (Nat.zero_le _)).mp hFirst
  exact he

def resourceSample (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) (hFirst : decode 0 ≤ budget) (K attempts : ℕ)
    (bits : Fin (prefixSampleBitBudget C blocks.length K attempts) → Bool) : Fin (C + 1) :=
  prefixSample C blocks hp hw (MonotoneResourceCuts.cap C decode budget)
    (resourceCap_nonnegative C decode hm budget hFirst) K attempts bits

theorem resourceSample_feasible (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) (hFirst : decode 0 ≤ budget) (K attempts : ℕ)
    (bits : Fin (prefixSampleBitBudget C blocks.length K attempts) → Bool) :
    decode (resourceSample C blocks hp hw decode hm budget hFirst K attempts bits).val ≤ budget := by
  apply (MonotoneResourceCuts.cap_contract C decode hm budget _ (by omega)).mpr
  exact prefixSample_feasible C blocks hp hw _ (resourceCap_nonnegative C decode hm budget hFirst) K attempts bits

theorem resourceSample_mean_error (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) (hFirst : decode 0 ≤ budget) (K attempts : ℕ) (test : Fin (C + 1) → ℝ)
    (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (prefixSampleBitBudget C blocks.length K attempts)).mean
      (fun bits => test (resourceSample C blocks hp hw decode hm budget hFirst K attempts bits)) -
      (∑ code : Fin (C + 1), if decode code.val ≤ budget then (labelMass blocks code.val : ℝ) * test code else 0) /
        ((decodedFamily C blocks (fun b hb => (hw b hb).le) decode).prefixMass budget : ℝ)| ≤
          1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts := by
  have he := prefixSample_weighted_prefix_error C blocks hp hw (MonotoneResourceCuts.cap C decode budget)
    (resourceCap_nonnegative C decode hm budget hFirst) K attempts test hTest
  rw [decodedFamily_prefixMass C blocks hp (fun b hb => (hw b hb).le) decode hm budget]
  have hSum : (∑ code : Fin (C + 1), if decode code.val ≤ budget then (labelMass blocks code.val : ℝ) * test code else 0) =
      ∑ code : Fin (C + 1), if (code.val : ℤ) ≤ MonotoneResourceCuts.cap C decode budget
        then (labelMass blocks code.val : ℝ) * test code else 0 := by
    apply Finset.sum_congr rfl
    intro code _
    simp only [MonotoneResourceCuts.cap_contract C decode hm budget code.val (by omega)]
  rw [hSum]
  exact he

end Blotto.ImplicitLeafCounts
