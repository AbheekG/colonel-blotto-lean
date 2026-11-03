import Blotto.BinaryCategoricalPreparationWork
import Blotto.BinaryCoinWordWork

/-! The native categorical shared-cap loop retains actual preparation, stored
probability padding and fixed-width residual coin words. Its output, exhaustion
and absolute position are exactly the retained native runner. Primitive work
is charged along the same path; metadata/physical storage remain separate. -/

namespace Blotto.BinaryCategoricalRunWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryCategoricalPreparation BinaryCategoricalRun
open BinaryCategoricalUnitLattice BinaryCategoricalPreparationWork

def paddingWork {α : Type*} (choice : Choice α) : ℕ :=
  12 * (max choice.probability.numerator.length choice.probability.denominator.length + 1)

def runIndexed {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : Cursor α) (pos : ℕ) (hp : pos ≤ N) : (Option α × ℕ) × ℕ :=
  match cursor with
  | .selected value => ((some value, pos), 1)
  | .remaining weights =>
      let prepared := prepareWithWork fallback weights
      match hs : prepared.1 with
      | .done value => ((some value, pos), prepared.2 + 1)
      | .ask choice =>
          let later := runIndexed fallback N bits (pending choice) pos hp
          (later.1, prepared.2 + paddingWork choice + later.2 + 1)
  | .coin choice a b hb hab =>
      let body := FixedWordCoin.bodyWork a b + 2
      if hz : a.isZero = true then
        let later := runIndexed fallback N bits (.remaining choice.rest) pos hp
        (later.1, body + later.2)
      else if he : a.same b = true then
        let later := runIndexed fallback N bits (.selected choice.head.1) pos hp
        (later.1, body + later.2)
      else if hRead : pos < N then
        let bit := bits ⟨pos, hRead⟩
        let next := a.coinStep b
        have hlt : a.value < b.value := lt_of_le_of_ne hab (fun h => he ((a.same_value b).mpr h))
        if bit = next.1 then
          let later := runIndexed fallback N bits (.coin choice next.2 b hb (a.coinStep_normalized b hlt).le)
            (pos + 1) (by omega)
          (later.1, body + later.2)
        else
          let later := runIndexed fallback N bits
            (if bit then .remaining choice.rest else .selected choice.head.1) (pos + 1) (by omega)
          (later.1, body + later.2)
      else ((none, pos), body)
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW := prepared_choice_weights fallback weights choice hs
    simp only [pending, Cursor.rank]
    rw [hW]
    omega
  · apply Prod.Lex.right
    have hL := rest_length choice
    simp only [Cursor.rank]
    omega
  · apply Prod.Lex.right
    simp only [Cursor.rank]
    rw [choice.head_pair]
    simp only [List.length_cons]
    omega
  all_goals apply Prod.Lex.left
  all_goals omega

theorem runIndexed_state {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : Cursor α) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexed fallback N bits cursor pos hp).1 = BinaryCategoricalRun.runIndexed fallback N bits cursor pos hp := by
  cases cursor with
  | selected value => unfold runIndexed BinaryCategoricalRun.runIndexed; rfl
  | remaining weights =>
      conv_lhs => unfold runIndexed
      conv_rhs => unfold BinaryCategoricalRun.runIndexed
      rw [← prepareWithWork_state fallback weights]
      dsimp only
      cases hs : (prepareWithWork fallback weights).1 with
      | done value => rfl
      | ask choice => exact runIndexed_state fallback N bits (pending choice) pos hp
  | coin choice a b hb hab =>
      conv_lhs => unfold runIndexed
      conv_rhs => unfold BinaryCategoricalRun.runIndexed
      dsimp only
      split
      · exact runIndexed_state fallback N bits (.remaining choice.rest) pos hp
      · split
        · exact runIndexed_state fallback N bits (.selected choice.head.1) pos hp
        · split
          · split
            · exact runIndexed_state fallback N bits _ (pos + 1) _
            · exact runIndexed_state fallback N bits _ (pos + 1) _
          · rfl
termination_by (N - pos, cursor.rank)
decreasing_by
  · apply Prod.Lex.right
    have hW := prepared_choice_weights fallback weights choice hs
    simp only [pending, Cursor.rank]
    rw [hW]
    omega
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       have hL := rest_length choice
       simp only [Cursor.rank]
       rw [choice.head_pair] at hL ⊢
       simp only [List.length_cons] at hL ⊢
       omega)

def BoundedCursor {α : Type*} (D M : ℕ) : Cursor α → Prop
  | .selected _ => True
  | .remaining weights => UnitLattice D weights ∧ weights.items.length ≤ M
  | .coin (w := w) choice _ _ _ _ => UnitLattice D choice.weights ∧ choice.weights.items.length ≤ M ∧
      w ≤ 5 + 8 * binaryWordWidth D

def bodyBound (D : ℕ) : ℕ := 24 * (5 + 8 * binaryWordWidth D) + 30
def choiceBound (D M : ℕ) : ℕ := preparationBound D M + 12 * (6 + 8 * binaryWordWidth D) + bodyBound D + 2

def allowance {α : Type*} (D M remaining : ℕ) : Cursor α → ℕ
  | .selected _ => 1
  | .remaining weights => (weights.items.length + 1) * choiceBound D M + remaining * bodyBound D + 1
  | .coin choice _ _ _ _ => choice.weights.items.length * choiceBound D M + (remaining + 1) * bodyBound D + 1

theorem pending_bounded {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (choice : Choice α)
    (h : UnitLattice D choice.weights) (hLength : choice.weights.items.length ≤ M) :
    BoundedCursor D M (pending choice) := by
  have hw := choice_probability_width D hD choice h
  exact ⟨h, hLength, hw⟩

theorem rest_bounded {α : Type*} (D M : ℕ) (choice : Choice α)
    (h : UnitLattice D choice.weights) (hLength : choice.weights.items.length ≤ M) :
    BoundedCursor D M (.remaining choice.rest) := by
  have hl := rest_length choice
  exact ⟨choice_rest_unit D choice h, by omega⟩

theorem body_bound {α : Type*} (D : ℕ) {w : ℕ} (_choice : Choice α) (a b : FixedBinaryWord w)
    (hw : w ≤ 5 + 8 * binaryWordWidth D) : FixedWordCoin.bodyWork a b + 2 ≤ bodyBound D := by
  have h := FixedWordCoin.bodyWork_bound a b
  rw [FixedWordCoin.bodyAllowance_eq] at h
  unfold bodyBound
  omega

theorem preparationBound_mono (D : ℕ) {length M : ℕ} (h : length ≤ M) :
    preparationBound D length ≤ preparationBound D M := by
  unfold preparationBound
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.add_le_add_right h 1)) _

theorem padding_bound {α : Type*} (D : ℕ) (hD : 0 < D) (choice : Choice α)
    (h : UnitLattice D choice.weights) : paddingWork choice ≤ 12 * (6 + 8 * binaryWordWidth D) := by
  have hw := choice_probability_width D hD choice h
  unfold paddingWork
  exact Nat.mul_le_mul_left 12 (by change width choice.probability + 1 ≤ _; omega)

theorem prepared_credit {α : Type*} (D : ℕ) (hD : 0 < D) (M remaining : ℕ) (fallback : α)
    (weights : WeightList α) (h : UnitLattice D weights) (hLength : weights.items.length ≤ M)
    (choice : Choice α) (hs : (prepareWithWork fallback weights).1 = .ask choice) :
    (prepareWithWork fallback weights).2 + paddingWork choice +
      allowance D M remaining (pending choice) + 1 ≤ allowance D M remaining (.remaining weights) := by
  have hW := prepared_choice_weights fallback weights choice hs
  have hPrep := (prepareWithWork_bound D hD fallback weights h).trans (preparationBound_mono D hLength)
  have hChoice : UnitLattice D choice.weights := hW.symm ▸ h
  have hPad := padding_bound D hD choice hChoice
  unfold allowance pending
  dsimp only
  rw [hW]
  unfold choiceBound
  nlinarith

theorem done_credit {α : Type*} (D : ℕ) (hD : 0 < D) (M remaining : ℕ) (fallback : α)
    (weights : WeightList α) (h : UnitLattice D weights) (hLength : weights.items.length ≤ M) :
    (prepareWithWork fallback weights).2 + 1 ≤ allowance D M remaining (.remaining weights) := by
  have hp := (prepareWithWork_bound D hD fallback weights h).trans (preparationBound_mono D hLength)
  have hm : 1 ≤ weights.items.length + 1 := by omega
  have hScale := Nat.mul_le_mul_right (choiceBound D M) hm
  unfold allowance choiceBound at ⊢ hScale
  nlinarith

theorem zero_credit {α : Type*} (D M remaining : ℕ) (choice : Choice α) {w : ℕ} (a b : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value) (hw : w ≤ 5 + 8 * binaryWordWidth D) :
    FixedWordCoin.bodyWork a b + 2 + allowance D M remaining (.remaining choice.rest) ≤
      allowance D M remaining (.coin choice a b hb hab) := by
  have hl := rest_length choice
  have hp := body_bound D choice a b hw
  simp only [allowance]
  rw [show choice.rest.items.length + 1 = choice.weights.items.length from hl]
  nlinarith

theorem selected_credit {α : Type*} (D M remaining : ℕ) (choice : Choice α) {w : ℕ} (a b : FixedBinaryWord w)
    (hb : 0 < b.value) (hab : a.value ≤ b.value) (hw : w ≤ 5 + 8 * binaryWordWidth D) :
    FixedWordCoin.bodyWork a b + 2 + allowance D M remaining (.selected choice.head.1) ≤
      allowance D M remaining (.coin choice a b hb hab) := by
  have hp := body_bound D choice a b hw
  unfold allowance
  nlinarith

theorem residual_credit {α : Type*} (D M N pos : ℕ) (hRead : pos < N) (choice : Choice α)
    {w : ℕ} (a b next : FixedBinaryWord w) (hb : 0 < b.value) (hab : a.value ≤ b.value)
    (hnext : next.value ≤ b.value) (hw : w ≤ 5 + 8 * binaryWordWidth D) :
    FixedWordCoin.bodyWork a b + 2 + allowance D M (N - (pos + 1)) (.coin choice next b hb hnext) ≤
      allowance D M (N - pos) (.coin choice a b hb hab) := by
  have hp := body_bound D choice a b hw
  have he : N - pos = N - (pos + 1) + 1 := by omega
  unfold allowance
  rw [he]
  nlinarith

theorem runIndexed_bound {α : Type*} (D : ℕ) (hD : 0 < D) (M : ℕ) (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : Cursor α) (pos : ℕ) (hp : pos ≤ N) (h : BoundedCursor D M cursor) :
    (runIndexed fallback N bits cursor pos hp).2 ≤ allowance D M (N - pos) cursor := by
  cases cursor with
  | selected value => simp [runIndexed, allowance]
  | remaining weights =>
      unfold runIndexed
      dsimp only
      cases hs : (prepareWithWork fallback weights).1 with
      | done value =>
          dsimp only
          exact done_credit D hD M (N - pos) fallback weights h.1 h.2
      | ask choice =>
          dsimp only
          have hW := prepared_choice_weights fallback weights choice hs
          have hUnit : UnitLattice D choice.weights := hW.symm ▸ h.1
          have hLength : choice.weights.items.length ≤ M := hW.symm ▸ h.2
          have hNext := pending_bounded D hD M choice hUnit hLength
          have ih := runIndexed_bound D hD M fallback N bits (pending choice) pos hp hNext
          have hc := prepared_credit D hD M (N - pos) fallback weights h.1 h.2 choice hs
          omega
  | @coin w choice a b hb hab =>
      obtain ⟨hUnit, hLength, hWidth⟩ := h
      unfold runIndexed
      dsimp only
      split
      · have ih := runIndexed_bound D hD M fallback N bits (.remaining choice.rest) pos hp
          (rest_bounded D M choice hUnit hLength)
        have hc := zero_credit D M (N - pos) choice a b hb hab hWidth
        omega
      · rename_i hz
        split
        · have ih := runIndexed_bound D hD M fallback N bits (.selected choice.head.1) pos hp trivial
          have hc := selected_credit D M (N - pos) choice a b hb hab hWidth
          omega
        · rename_i he
          split
          · rename_i hRead
            split
            · have hlt : a.value < b.value := by
                apply lt_of_le_of_ne hab
                intro hv
                have ht := (a.same_value b).mpr hv
                exact he ht
              have ih := runIndexed_bound D hD M fallback N bits
                (.coin choice (a.coinStep b).2 b hb (a.coinStep_normalized b hlt).le) (pos + 1) (by omega)
                ⟨hUnit, hLength, hWidth⟩
              have hc := residual_credit D M N pos hRead choice a b (a.coinStep b).2 hb hab
                (a.coinStep_normalized b hlt).le hWidth
              omega
            · split
              · have ih := runIndexed_bound D hD M fallback N bits (.remaining choice.rest) (pos + 1) (by omega)
                  (rest_bounded D M choice hUnit hLength)
                have hc := zero_credit D M (N - pos) choice a b hb hab hWidth
                have hm : allowance D M (N - (pos + 1)) (.remaining choice.rest) ≤
                    allowance D M (N - pos) (.remaining choice.rest) := by
                  unfold allowance
                  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _) _
                omega
              · have ih := runIndexed_bound D hD M fallback N bits (.selected choice.head.1) (pos + 1) (by omega) trivial
                have hc := selected_credit D M (N - pos) choice a b hb hab hWidth
                simp only [allowance] at ih hc ⊢
                omega
          · have hc := body_bound D choice a b hWidth
            unfold allowance
            nlinarith
termination_by (N - pos, cursor.rank)
decreasing_by
  all_goals simp_all only [Cursor.rank]
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right
       try simp only [pending]
       first
       | (have hW := prepared_choice_weights fallback weights choice hs; rw [hW]; omega)
       | (have hl := rest_length choice; rw [choice.head_pair] at hl ⊢; simp only [List.length_cons] at hl ⊢; omega))

end Blotto.BinaryCategoricalRunWork
