import Blotto.FixedDenominatorCoin
import Blotto.AdaptiveChoiceTree

/-! Shared-cap sampling with fixed-denominator integer digits at every
adaptive node. This is the operational refinement of the rational tree
semantics; preparing a compact PRG state machine is a separate step. -/

namespace Blotto

inductive WordChoiceTree (α : Type*) where
  | leaf (value : α)
  | fork (numerator denominator : ℕ) (denominator_pos : 0 < denominator)
      (normalized : numerator ≤ denominator) (upper lower : WordChoiceTree α)

namespace WordChoiceTree

def height {α : Type*} : WordChoiceTree α → ℕ
  | .leaf _ => 0
  | .fork _ _ _ _ upper lower => 1 + max upper.height lower.height

def decode {α : Type*} : WordChoiceTree α → AdaptiveChoiceTree α
  | .leaf x => .leaf x
  | .fork a b hb hab upper lower => .fork ((a : ℚ) / b) (by
      have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
      exact ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩) upper.decode lower.decode

theorem decode_height {α : Type*} (T : WordChoiceTree α) : T.decode.height = T.height := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl => simp only [decode, AdaptiveChoiceTree.height, height, hu, hl]

def sample {α : Type*} (R : ℕ) (T : WordChoiceTree α) (bits : Fin R → Bool) : Option α × ℕ :=
  match T with
  | .leaf x => (some x, 0)
  | .fork a b hb hab upper lower =>
    if a = 0 then sample R lower bits else if b ≤ a then sample R upper bits else
      match R with
      | 0 => (none, 0)
      | r + 1 =>
        if bits 0 = denominatorDigit a b then
          let result := sample r (.fork (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (Fin.tail bits)
          (result.1, result.2 + 1)
        else
          let result := sample r (if bits 0 then lower else upper) (Fin.tail bits)
          (result.1, result.2 + 1)
termination_by (R, T.height)
decreasing_by
  all_goals simp_wf
  all_goals simp only [height]
  all_goals omega

theorem sample_refines {α : Type*} (R : ℕ) (T : WordChoiceTree α) (bits : Fin R → Bool) :
    T.sample R bits = T.decode.sample R bits := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf x => simp only [sample, decode, AdaptiveChoiceTree.sample]
    | fork a b hb hab upper lower hu hl =>
      have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
      have h0 : ((a : ℚ) / b ≤ 0) ↔ a = 0 := by
        rw [div_le_iff₀ hbQ, zero_mul]
        exact_mod_cast (Nat.le_zero : a ≤ 0 ↔ a = 0)
      have h1 : ((1 : ℚ) ≤ (a : ℚ) / b) ↔ b ≤ a := by
        rw [le_div_iff₀ hbQ, one_mul]
        norm_cast
      conv_lhs => unfold sample
      conv_rhs => rw [decode]; unfold AdaptiveChoiceTree.sample
      simp only [h0, h1, probabilityDigit_ratio a b hb]
      by_cases ha0 : a = 0
      · simp only [ha0, ite_true]
        exact hl
      by_cases hba : b ≤ a
      · simp only [ha0, hba, ite_false, ite_true]
        exact hu
      simp only [ha0, hba, ite_false]
      cases R with
      | zero => rfl
      | succ r =>
        dsimp only
        by_cases hd : bits 0 = denominatorDigit a b
        · simp only [hd, ite_true]
          have he := ih r (by omega) (.fork (numeratorResidual a b) b hb (numeratorResidual_bounds a b hab) upper lower) (Fin.tail bits)
          simp only [decode] at he
          have hnode : AdaptiveChoiceTree.fork ((numeratorResidual a b : ℚ) / b) (by
              have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
              exact ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast numeratorResidual_bounds a b hab)⟩)
              upper.decode lower.decode =
              AdaptiveChoiceTree.fork (coinResidual ((a : ℚ) / b)) (coinResidual_bounds (by
                exact ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩)) upper.decode lower.decode := by
            simp only [coinResidual_ratio a b hb]
          rw [hnode] at he
          exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1)) he
        · simp only [hd, ite_false]
          by_cases hbit : bits 0 = true
          · simp only [hbit, ite_true]
            exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1)) (ih r (by omega) lower (Fin.tail bits))
          · simp only [hbit]
            exact congrArg (fun result : Option α × ℕ => (result.1, result.2 + 1)) (ih r (by omega) upper (Fin.tail bits))

theorem sample_bits_le {α : Type*} (R : ℕ) (T : WordChoiceTree α) (bits : Fin R → Bool) : (T.sample R bits).2 ≤ R := by
  rw [T.sample_refines]
  exact T.decode.sample_bits_le R bits

end WordChoiceTree
end Blotto
