import Blotto.MonotoneCodeSearch
import Blotto.ImplicitLeafUpdate

/-! Actual binary searches derive weak/strict rational-resource cuts and the
exact opposing half-tie loss. Monotonic decoding on valid codes is explicit;
no particular Farey/predecessor routine or its cost is assumed implemented. -/

namespace Blotto.MonotoneResourceCuts
open MonotoneCodeSearch

def MonotoneDecode (C : ℕ) (decode : ℕ → ℚ) : Prop :=
  ∀ first second, first ≤ second → second ≤ C → decode first ≤ decode second

def weakPredicate (decode : ℕ → ℚ) (opponent : ℚ) (code : ℕ) : Bool := decide (opponent ≤ decode code)
def strictPredicate (decode : ℕ → ℚ) (opponent : ℚ) (code : ℕ) : Bool := decide (opponent < decode code)
def weak (C : ℕ) (decode : ℕ → ℚ) (opponent : ℚ) : ℕ × ℕ := first C (weakPredicate decode opponent)
def strict (C : ℕ) (decode : ℕ → ℚ) (opponent : ℚ) : ℕ × ℕ := first C (strictPredicate decode opponent)
def cap (C : ℕ) (decode : ℕ → ℚ) (budget : ℚ) : ℤ := (strict C decode budget).1 - (1 : ℤ)

theorem weak_monotone (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (opponent : ℚ) :
    IsMonotone C (weakPredicate decode opponent) := by
  intro i j hij hj hp
  apply decide_eq_true
  have hi : opponent ≤ decode i := of_decide_eq_true hp
  exact hi.trans (hm i j hij hj)

theorem strict_monotone (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (opponent : ℚ) :
    IsMonotone C (strictPredicate decode opponent) := by
  intro i j hij hj hp
  apply decide_eq_true
  have hi : opponent < decode i := of_decide_eq_true hp
  exact hi.trans_le (hm i j hij hj)

theorem weak_contract (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (opponent : ℚ) :
    (weak C decode opponent).1 ≤ C + 1 ∧
      (∀ code ≤ C, opponent ≤ decode code ↔ (weak C decode opponent).1 ≤ code) := by
  simpa only [weak, weakPredicate, decide_eq_true_eq] using
    first_contract C (weakPredicate decode opponent) (weak_monotone C decode hm opponent)

theorem strict_contract (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (opponent : ℚ) :
    (strict C decode opponent).1 ≤ C + 1 ∧
      (∀ code ≤ C, opponent < decode code ↔ (strict C decode opponent).1 ≤ code) := by
  simpa only [strict, strictPredicate, decide_eq_true_eq] using
    first_contract C (strictPredicate decode opponent) (strict_monotone C decode hm opponent)

theorem cuts_order (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (opponent : ℚ) :
    (weak C decode opponent).1 ≤ (strict C decode opponent).1 := by
  have hw := weak_contract C decode hm opponent
  have hs := strict_contract C decode hm opponent
  by_cases hLast : (strict C decode opponent).1 = C + 1
  · rw [hLast]
    exact hw.1
  · have hc : (strict C decode opponent).1 ≤ C := by omega
    have hp := (hs.2 _ hc).mpr le_rfl
    exact (hw.2 _ hc).mp hp.le

theorem cap_contract (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode) (budget : ℚ)
    (code : ℕ) (hc : code ≤ C) : decode code ≤ budget ↔ (code : ℤ) ≤ cap C decode budget := by
  have hs := (strict_contract C decode hm budget).2 code hc
  have hn : decode code ≤ budget ↔ code < (strict C decode budget).1 := by
    rw [← not_lt, hs, not_le]
  rw [hn]
  unfold cap
  omega

theorem cuts_visits (C : ℕ) (decode : ℕ → ℚ) (opponent : ℚ) :
    (weak C decode opponent).2 + (strict C decode opponent).2 ≤ 2 * binaryWordWidth (C + 1) := by
  have hw := first_visits C (weakPredicate decode opponent)
  have hs := first_visits C (strictPredicate decode opponent)
  change (weak C decode opponent).2 ≤ _ at hw
  change (strict C decode opponent).2 ≤ _ at hs
  omega

theorem regionLoss_exact (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (opponent : ℚ) (code : ℕ) (hc : code ≤ C) :
    ImplicitLeafCounts.regionLoss (weak C decode opponent).1 (strict C decode opponent).1 code =
      SparseMW.rationalShare opponent (decode code) := by
  have hw := (weak_contract C decode hm opponent).2 code hc
  have hs := (strict_contract C decode hm opponent).2 code hc
  have hWeak : (code : ℤ) < (weak C decode opponent).1 ↔ decode code < opponent := by
    have he : code < (weak C decode opponent).1 ↔ decode code < opponent := by
      rw [← not_le, ← hw, not_le]
    exact_mod_cast he
  have hStrict : (code : ℤ) < (strict C decode opponent).1 ↔ decode code ≤ opponent := by
    have he : code < (strict C decode opponent).1 ↔ decode code ≤ opponent := by
      rw [← not_le, ← hs, not_lt]
    exact_mod_cast he
  unfold ImplicitLeafCounts.regionLoss SparseMW.rationalShare
  simp only [hWeak, hStrict]
  by_cases hLt : decode code < opponent
  · simp only [hLt, ite_true]
  · by_cases hEq : decode code = opponent
    · simp [hEq]
    · have hGt : opponent < decode code := lt_of_le_of_ne (le_of_not_gt hLt) (Ne.symm hEq)
      simp only [hLt, not_le_of_gt hGt, Ne.symm hEq, ite_false]

end Blotto.MonotoneResourceCuts
