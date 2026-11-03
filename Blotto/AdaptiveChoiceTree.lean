import Blotto.RationalCoin
import Blotto.FairBitExpectation

/-! Finite adaptive rational-choice semantics and a shared-cap digit
interpreter. Child probabilities may depend arbitrarily on earlier outcomes.
The interpreter follows one path and reuses the remaining bit vector; the
tree itself is proof semantics, not an asserted compact PRG representation. -/

namespace Blotto

inductive AdaptiveChoiceTree (α : Type*) where
  | leaf (value : α)
  | fork (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : AdaptiveChoiceTree α)

namespace AdaptiveChoiceTree

def height {α : Type*} : AdaptiveChoiceTree α → ℕ
  | .leaf _ => 0
  | .fork _ _ a b => 1 + max a.height b.height

def ForLeaves {α : Type*} (P : α → Prop) : AdaptiveChoiceTree α → Prop
  | .leaf x => P x
  | .fork _ _ a b => a.ForLeaves P ∧ b.ForLeaves P

def sample {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (bits : Fin R → Bool) : Option α × ℕ :=
  match T with
  | .leaf x => (some x, 0)
  | .fork p hp upper lower =>
    if p ≤ 0 then sample R lower bits else if 1 ≤ p then sample R upper bits else
      match R with
      | 0 => (none, 0)
      | r + 1 =>
        if bits 0 = probabilityDigit p then
          let result := sample r (.fork (coinResidual p) (coinResidual_bounds hp) upper lower) (Fin.tail bits)
          (result.1, result.2 + 1)
        else
          let result := sample r (if bits 0 then lower else upper) (Fin.tail bits)
          (result.1, result.2 + 1)
termination_by (R, T.height)
decreasing_by
  all_goals simp_wf
  all_goals simp only [height]
  all_goals omega

theorem sample_bits_le {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (bits : Fin R → Bool) :
    (T.sample R bits).2 ≤ R := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf x => simp [sample]
    | fork p hp upper lower hu hl =>
      unfold sample
      split_ifs with h0 h1
      · exact hl
      · exact hu
      · cases R with
        | zero => simp
        | succ r =>
          dsimp only
          split_ifs
          · exact Nat.succ_le_succ (ih r (by omega) _ _)
          · exact Nat.succ_le_succ (ih r (by omega) _ _)
          · exact Nat.succ_le_succ (ih r (by omega) _ _)

theorem sample_none_bits {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (bits : Fin R → Bool)
    (hn : (T.sample R bits).1 = none) : (T.sample R bits).2 = R := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf x => simp [sample] at hn
    | fork p hp upper lower hu hl =>
      unfold sample at hn ⊢
      by_cases h0 : p ≤ 0
      · simp only [h0, ite_true] at hn ⊢
        exact hl hn
      by_cases h1 : 1 ≤ p
      · simp only [h0, h1, ite_false, ite_true] at hn ⊢
        exact hu hn
      simp only [h0, h1, ite_false] at hn ⊢
      cases R with
      | zero => rfl
      | succ r =>
        dsimp only at hn ⊢
        by_cases hd : bits 0 = probabilityDigit p
        · simp only [hd, ite_true] at hn ⊢
          exact congrArg (fun n => n + 1) (ih r (by omega) _ _ hn)
        · simp only [hd, ite_false] at hn ⊢
          exact congrArg (fun n => n + 1) (ih r (by omega) _ _ hn)

theorem sample_forLeaves {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (bits : Fin R → Bool)
    (P : α → Prop) (hT : T.ForLeaves P) {x : α} (hx : (T.sample R bits).1 = some x) : P x := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf y =>
      have he : y = x := by simpa only [sample, Option.some.injEq] using hx
      exact he ▸ hT
    | fork p hp upper lower hu hl =>
      unfold sample at hx
      by_cases h0 : p ≤ 0
      · apply hl hT.2
        simpa only [h0, ite_true] using hx
      by_cases h1 : 1 ≤ p
      · apply hu hT.1
        simpa only [h0, h1, ite_false, ite_true] using hx
      simp only [h0, h1, ite_false] at hx
      cases R with
      | zero => simp at hx
      | succ r =>
        dsimp only at hx
        by_cases hd : bits 0 = probabilityDigit p
        · simp only [hd, ite_true] at hx
          exact ih r (by omega) (.fork (coinResidual p) (coinResidual_bounds hp) upper lower) (Fin.tail bits) hT hx
        · simp only [hd, ite_false] at hx
          have ht : (if bits 0 then lower else upper).ForLeaves P := by
            split_ifs
            · exact hT.2
            · exact hT.1
          exact ih r (by omega) _ _ ht hx

end AdaptiveChoiceTree
end Blotto
