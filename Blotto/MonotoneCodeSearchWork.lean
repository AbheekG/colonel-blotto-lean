import Blotto.MonotoneResourceCuts

/-! Binary code search with an explicit predicate callback price. The observer
charges comparison/address/interval arithmetic as named real-RAM operations.
Finite binary costs of those interval operations and a Farey callback remain
separate, rather than silently identifying comparisons with bit runtime. -/

namespace Blotto.MonotoneCodeSearch

def runWithWork : ℕ → (ℕ → Bool) → (ℕ → ℕ) → ℕ → ℕ → (ℕ × ℕ) × ℕ
  | 0, _, _, lo, _hi => ((lo, 0), 2)
  | fuel + 1, predicate, price, lo, hi =>
      if lo < hi then
        let mid := lo + (hi - lo) / 2
        let next := if predicate mid then runWithWork fuel predicate price lo mid
          else runWithWork fuel predicate price (mid + 1) hi
        ((next.1.1, next.1.2 + 1), price mid + 10 + next.2)
      else ((lo, 0), 2)

theorem runWithWork_state (fuel : ℕ) (predicate : ℕ → Bool) (price : ℕ → ℕ) (lo hi : ℕ) :
    (runWithWork fuel predicate price lo hi).1 = search fuel predicate lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    simp only [runWithWork, search]
    split
    · split <;> dsimp only <;> rw [ih]
    · rfl

theorem runWithWork_bound (fuel C : ℕ) (predicate : ℕ → Bool) (price : ℕ → ℕ)
    (lo hi P : ℕ) (hBracket : lo ≤ hi ∧ hi ≤ C + 1) (hPrice : ∀ code ≤ C, price code ≤ P) :
    (runWithWork fuel predicate price lo hi).2 ≤ fuel * (P + 10) + 2 := by
  induction fuel generalizing lo hi with
  | zero => simp [runWithWork]
  | succ fuel ih =>
    simp only [runWithWork]
    split
    · rename_i hActive
      let mid := lo + (hi - lo) / 2
      have hmLo : lo ≤ mid := by dsimp only [mid]; omega
      have hmHi : mid < hi := by dsimp only [mid]; omega
      have hc : mid ≤ C := by omega
      have hp := hPrice mid hc
      split
      · have he := ih lo mid ⟨hmLo, by omega⟩
        dsimp only [mid] at hp he
        dsimp only
        nlinarith
      · have he := ih (mid + 1) hi ⟨by omega, hBracket.2⟩
        dsimp only [mid] at hp he
        dsimp only
        nlinarith
    · dsimp only
      omega

def firstWithWork (C : ℕ) (predicate : ℕ → Bool) (price : ℕ → ℕ) : (ℕ × ℕ) × ℕ :=
  runWithWork (binaryWordWidth (C + 1)) predicate price 0 (C + 1)

theorem firstWithWork_contract (C : ℕ) (predicate : ℕ → Bool) (price : ℕ → ℕ)
    (P : ℕ) (hPrice : ∀ code ≤ C, price code ≤ P) :
    (firstWithWork C predicate price).1 = first C predicate ∧
      (firstWithWork C predicate price).2 ≤ binaryWordWidth (C + 1) * (P + 10) + 2 :=
  ⟨runWithWork_state _ _ _ _ _, runWithWork_bound _ C _ _ _ _ P ⟨Nat.zero_le _, le_rfl⟩ hPrice⟩

end Blotto.MonotoneCodeSearch
